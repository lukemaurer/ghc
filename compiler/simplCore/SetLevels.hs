{-
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998

\section{SetLevels}

                ***************************
                        Overview
                ***************************

1. We attach binding levels to Core bindings, in preparation for floating
   outwards (@FloatOut@).

2. We also let-ify many expressions (notably case scrutinees), so they
   will have a fighting chance of being floated sensible.

3. Note [Need for cloning during float-out]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   We clone the binders of any floatable let-binding, so that when it is
   floated out it will be unique. Example
      (let x=2 in x) + (let x=3 in x)
   we must clone before floating so we get
      let x1=2 in
      let x2=3 in
      x1+x2
  (Also, see Note [The Reason SetLevels Does Substitution].)

   NOTE: this can't be done using the uniqAway idea, because the variable
         must be unique in the whole program, not just its current scope,
         because two variables in different scopes may float out to the
         same top level place

   NOTE: Very tiresomely, we must apply this substitution to
         the rules stored inside a variable too.

   We do *not* clone top-level bindings, because some of them must not change,
   but we *do* clone bindings that are heading for the top level

4. Note [Binder-swap during float-out]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   In the expression
        case x of wild { p -> ...wild... }
   we substitute x for wild in the RHS of the case alternatives:
        case x of wild { p -> ...x... }
   This means that a sub-expression involving x is not "trapped" inside the RHS.
   And it's not inconvenient because we already have a substitution.

  Note that this is EXACTLY BACKWARDS from the what the simplifier does.
  The simplifier tries to get rid of occurrences of x, in favour of wild,
  in the hope that there will only be one remaining occurrence of x, namely
  the scrutinee of the case, and we can inline it.
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
module SetLevels (
        setLevels,

        Level(..), tOP_LEVEL,
        LevelledBind, LevelledExpr, LevelledBndr,
        FloatSpec(..), floatSpecLevel,

        incMinorLvl, ltMajLvl, ltLvl, isTopLvl
    ) where

#include "HsVersions.h"

import StaticFlags
import DynFlags

import CorePrep
import CoreSyn
import CoreUnfold       ( mkInlinableUnfolding )
import CoreMonad        ( FloatOutSwitches(..), FinalPassSwitches(..) )
import CoreUtils        ( exprType
                        , exprOkForSpeculation
                        , exprIsHNF
                        , exprIsBottom
                        , collectStaticPtrSatArgs
                        )
import CoreArity        ( exprBotStrictness_maybe )
import CoreFVs          -- all of it
import Coercion         ( tyCoVarsOfCoDSet )
import CoreSubst
import CoreCxts
import MkCore           ( sortQuantVars )

import SMRep            ( WordOff )
import StgCmmArgRep     ( ArgRep(P), argRepSizeW, toArgRep )
import StgCmmLayout     ( mkVirtHeapOffsets )
import StgCmmClosure    ( idPrimRep, addIdReps )

import qualified TidyPgm

import Demand           ( isStrictDmd, splitStrictSig )
import Id
import IdInfo
import Var
import VarSet
import VarEnv
import Literal          ( litIsTrivial )
import Demand           ( StrictSig )
import Name             ( getOccName, mkSystemVarName )
import OccName          ( occNameString )
import Type             ( isUnliftedType, Type, mkLamTypes
                        , tyCoVarsOfTypeDSet )
import RepType          ( typePrimRep )
import BasicTypes       ( Arity, RecFlag(..), isNonRec, isRec )
import UniqSupply
import Util
import Outputable
import FastString
import FV

import MonadUtils       ( mapAndUnzipM )

import Data.Maybe       ( isJust, mapMaybe )
import qualified Data.List

import qualified Control.Monad

{-
************************************************************************
*                                                                      *
\subsection{Level numbers}
*                                                                      *
************************************************************************
-}

type LevelledExpr = ExprWithCxts LevelledBndr
type LevelledBind = BindWithCxts LevelledBndr
type LevelledBndr = TaggedBndr FloatSpec

type MajorLevel = Int
data Level = Level MajorLevel -- Level number of enclosing lambdas
                   Int  -- Number of big-lambda and/or case expressions and/or
                        -- context boundaries between
                        -- here and the nearest enclosing lambda

data FloatSpec
  = FloatMe Level       -- Float to just inside the binding
                        --    tagged with this level
  | StayPut Level       -- Stay where it is; binding is
                        --     tagged with tihs level

floatSpecLevel :: FloatSpec -> Level
floatSpecLevel (FloatMe l) = l
floatSpecLevel (StayPut l) = l

{-
The {\em level number} on a (type-)lambda-bound variable is the
nesting depth of the (type-)lambda which binds it.  The outermost lambda
has level 1, so (Level 0 0) means that the variable is bound outside any lambda.

On an expression, it's the maximum level number of its free
(type-)variables.  On a let(rec)-bound variable, it's the level of its
RHS.  On a case-bound variable, it's the number of enclosing lambdas.

Top-level variables: level~0.  Those bound on the RHS of a top-level
definition but ``before'' a lambda; e.g., the \tr{x} in (levels shown
as ``subscripts'')...
\begin{verbatim}
a_0 = let  b_? = ...  in
           x_1 = ... b ... in ...
\end{verbatim}

The main function @lvlExpr@ carries a ``context level'' (@le_ctxt_lvl@).
That's meant to be the level number of the enclosing binder in the
final (floated) program.  If the level number of a sub-expression is
less than that of the context, then it might be worth let-binding the
sub-expression so that it will indeed float.

If you can float to level @Level 0 0@ worth doing so because then your
allocation becomes static instead of dynamic.  We always start with
context @Level 0 0@.


Note [FloatOut inside INLINE]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
@InlineCtxt@ very similar to @Level 0 0@, but is used for one purpose:
to say "don't float anything out of here".  That's exactly what we
want for the body of an INLINE, where we don't want to float anything
out at all.  See notes with lvlMFE below.

But, check this out:

-- At one time I tried the effect of not float anything out of an InlineMe,
-- but it sometimes works badly.  For example, consider PrelArr.done.  It
-- has the form         __inline (\d. e)
-- where e doesn't mention d.  If we float this to
--      __inline (let x = e in \d. x)
-- things are bad.  The inliner doesn't even inline it because it doesn't look
-- like a head-normal form.  So it seems a lesser evil to let things float.
-- In SetLevels we do set the context to (Level 0 0) when we get to an InlineMe
-- which discourages floating out.

So the conclusion is: don't do any floating at all inside an InlineMe.
(In the above example, don't float the {x=e} out of the \d.)

One particular case is that of workers: we don't want to float the
call to the worker outside the wrapper, otherwise the worker might get
inlined into the floated expression, and an importing module won't see
the worker at all.
-}

instance Outputable FloatSpec where
  ppr (FloatMe l) = char 'F' <> ppr l
  ppr (StayPut l) = ppr l

tOP_LEVEL :: Level
tOP_LEVEL   = Level 0 0

incMajorLvl :: Level -> Level
incMajorLvl (Level major _) = Level (major + 1) 0

incMinorLvl :: Level -> Level
incMinorLvl (Level major minor) = Level major (minor+1)

maxLvl :: Level -> Level -> Level
maxLvl l1@(Level maj1 min1) l2@(Level maj2 min2)
  | (maj1 > maj2) || (maj1 == maj2 && min1 > min2) = l1
  | otherwise                                      = l2

ltLvl :: Level -> Level -> Bool
ltLvl (Level maj1 min1) (Level maj2 min2)
  = (maj1 < maj2) || (maj1 == maj2 && min1 < min2)

ltMajLvl :: Level -> Level -> Bool
    -- Tells if one level belongs to a difft *lambda* level to another
ltMajLvl (Level maj1 _) (Level maj2 _) = maj1 < maj2

isTopLvl :: Level -> Bool
isTopLvl (Level 0 0) = True
isTopLvl _           = False

instance Outputable Level where
  ppr (Level maj min) = hcat [ char '<', int maj, char ',', int min, char '>' ]

instance Eq Level where
  (Level maj1 min1) == (Level maj2 min2) = maj1 == maj2 && min1 == min2

{-
************************************************************************
*                                                                      *
\subsection{Main level-setting code}
*                                                                      *
************************************************************************
-}

setLevels :: DynFlags
          -> FloatOutSwitches
          -> CoreProgram
          -> UniqSupply
          -> [LevelledBind]

setLevels dflags float_lams binds us
  = initLvl us (do_them init_env binds)
  where
    init_env = initialEnv dflags float_lams

    do_them :: LevelEnv -> [CoreBind] -> LvlM [LevelledBind]
    do_them _ [] = return []
    do_them env (b:bs)
      = do { b_with_cxts <- liftUs $ addContextsToTopBind b
           ; (lvld_bind, env') <- lvlTopBind dflags env b_with_cxts
           ; lvld_binds <- do_them env' bs
           ; return (lvld_bind : lvld_binds) }

lvlTopBind :: DynFlags -> LevelEnv -> CoreBindWithCxts -> LvlM (LevelledBind, LevelEnv)
lvlTopBind dflags env (NonRec bndr rhs)
  = do { rhs' <- lvlExpr env (analyzeFVs (initFVEnv $ finalPass env) rhs)
       ; let  -- lambda lifting impedes specialization, so: if the old
              -- RHS has an unstable unfolding that will survive
              -- TidyPgm, "stablize it" so that it ends up in the .hi
              -- file as-is, prior to LLF squeezing all of the juice out
              expose_all = gopt Opt_ExposeAllUnfoldings  dflags
              stab_bndr
                | isFinalPass env
                , gopt Opt_LLF_Stabilize dflags
                , snd $ TidyPgm.addExternal expose_all bndr
                , isUnstableUnfolding (realIdUnfolding bndr)
                  = bndr `setIdUnfolding` mkInlinableUnfolding dflags rhs
                | otherwise = bndr
       ; let (env', [bndr']) = substAndLvlBndrs NonRecursive env tOP_LEVEL
                                 [boringBinder stab_bndr]
       ; return (NonRec bndr' rhs', env') }

-- TODO, NSF 15 June 2014: shouldn't we stablize rec bindings too? They're not all loopbreakers
lvlTopBind _ env (Rec pairs)
  = do let (bndrs,rhss) = unzip pairs
           (env', bndrs') = substAndLvlBndrs Recursive env tOP_LEVEL
                              [ boringBinder bndr | bndr <- bndrs ]
       rhss' <- mapM (lvlExpr env' . analyzeFVs (initFVEnv $ finalPass env)) rhss
       return (Rec (bndrs' `zip` rhss'), env')

{-
************************************************************************
*                                                                      *
\subsection{Setting expression levels}
*                                                                      *
************************************************************************

Note [Floating over-saturated applications]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we see (f x y), and (f x) is a redex (ie f's arity is 1),
we call (f x) an "over-saturated application"

Should we float out an over-sat app, if can escape a value lambda?
It is sometimes very beneficial (-7% runtime -4% alloc over nofib -O2).
But we don't want to do it for class selectors, because the work saved
is minimal, and the extra local thunks allocated cost money.

Arguably we could float even class-op applications if they were going to
top level -- but then they must be applied to a constant dictionary and
will almost certainly be optimised away anyway.
-}

lvlExpr :: LevelEnv             -- Context
        -> CoreExprWithBoth     -- Input expression
        -> LvlM LevelledExpr    -- Result expression

{-
The @le_ctxt_lvl@ is, roughly, the level of the innermost enclosing
binder.  Here's an example

        v = \x -> ...\y -> let r = case (..x..) of
                                        ..x..
                           in ..

When looking at the rhs of @r@, @le_ctxt_lvl@ will be 1 because that's
the level of @r@, even though it's inside a level-2 @\y@.  It's
important that @le_ctxt_lvl@ is 1 and not 2 in @r@'s rhs, because we
don't want @lvlExpr@ to turn the scrutinee of the @case@ into an MFE
--- because it isn't a *maximal* free expression.

If there were another lambda in @r@'s rhs, it would get level-2 as well.
-}
lvlExpr env (splitAnnCxt -> InNewCxt (TB cid _) expr)
  = do let env' = enterTailContext env cid
           lvl' = le_ctxt_lvl env'
       expr' <- lvlExpr env' expr
       return (markCxt (TB cid (StayPut lvl')) (idType cid) expr')

lvlExpr env (_, AnnType ty)     = return (Type (substTy (le_subst env) ty))
lvlExpr env (_, AnnCoercion co) = return (Coercion (substCo (le_subst env) co))
lvlExpr env (_, AnnVar v)       = return (lookupVar env v)
lvlExpr _   (_, AnnLit lit)     = return (Lit lit)

lvlExpr env (_, AnnCast expr (_, co)) = do
    expr' <- lvlExpr env expr
    return (Cast expr' (substCo (le_subst env) co))

lvlExpr env (_, AnnTick tickish expr) = do
    expr' <- lvlExpr env expr
    return (Tick tickish expr')

lvlExpr env expr@(_, AnnApp _ _) = do
    let
      (fun, args) = collectAnnArgs expr
    --
    case fun of
      (_, AnnVar f) | floatOverSat env   -- See Note [Floating over-saturated applications]
                    , arity > 0
                    , arity < n_val_args
                    , Nothing <- isClassOpId_maybe f ->
        do
         let (lapp, rargs) = left (n_val_args - arity) expr []
         rargs' <- mapM (lvlMFE False env) rargs
         lapp' <- lvlMFE False env lapp
         return (foldl App lapp' rargs')
        where
         n_val_args = count (isValArg . deAnnotate) args
         arity = idArity f

         -- separate out the PAP that we are floating from the extra
         -- arguments, by traversing the spine until we have collected
         -- (n_val_args - arity) value arguments.
         left 0 e               rargs = (e, rargs)
         left n (_, AnnApp f a) rargs
            | isValArg (deAnnotate a) = left (n-1) f (a:rargs)
            | otherwise               = left n     f (a:rargs)
         left _ _ _                   = panic "SetLevels.lvlExpr.left"

         -- No PAPs that we can float: just carry on with the
         -- arguments and the function.
      _otherwise -> do
         args' <- mapM (lvlMFE False env) args
         fun'  <- lvlExpr env fun
         return (foldl App fun' args')

-- We don't split adjacent lambdas.  That is, given
--      \x y -> (x+1,y)
-- we don't float to give
--      \x -> let v = x+1 in \y -> (v,y)
-- Why not?  Because partial applications are fairly rare, and splitting
-- lambdas makes them more expensive.

lvlExpr env expr@(_, AnnLam {})
  = do { new_body <- lvlMFE True new_env body
       ; return (mkLams new_bndrs new_body) }
  where
    (bndrs, body)        = collectAnnBndrs expr
    (env1, bndrs1)       = substBndrsSL NonRecursive env bndrs
    (new_env, new_bndrs) = lvlLamBndrs env1 (le_ctxt_lvl env) bndrs1
        -- At one time we called a special verion of collectBinders,
        -- which ignored coercions, because we don't want to split
        -- a lambda like this (\x -> coerce t (\s -> ...))
        -- This used to happen quite a bit in state-transformer programs,
        -- but not nearly so much now non-recursive newtypes are transparent.
        -- [See SetLevels rev 1.50 for a version with this approach.]

lvlExpr env (_, AnnLet bind body)
  = do { (bind', new_env) <- lvlBind env bind
       ; body' <- lvlExpr new_env body
           -- No point in going via lvlMFE here.  If the binding is alive
           -- (mentioned in body), and the whole let-expression doesn't
           -- float, then neither will the body
       ; return (Let bind' body') }

lvlExpr env (_, AnnCase scrut case_bndr ty alts)
  = do { scrut' <- lvlMFE True env scrut
       ; lvlCase env (fvsOf scrut) scrut' case_bndr ty alts }

-------------------------------------------
lvlCase :: LevelEnv             -- Level of in-scope names/tyvars
        -> DVarSet              -- Free vars of input scrutinee
        -> LevelledExpr         -- Processed scrutinee
        -> InVar -> Type        -- Case binder and result type
        -> [CoreAltWithBoth]    -- Input alternatives
        -> LvlM LevelledExpr    -- Result expression
lvlCase env scrut_fvs scrut' case_bndr ty alts
  | [(con@(DataAlt {}), bs, body)] <- alts
  , exprOkForSpeculation scrut'   -- See Note [Check the output scrutinee for okForSpec]
  , not (isTopLvl dest_lvl)       -- Can't have top-level cases
  , not (floatTopLvlOnly env)     -- Can float anywhere
  =     -- See Note [Floating cases]
        -- Always float the case if possible
        -- Unlike lets we don't insist that it escapes a value lambda
    do { (env1, (case_bndr' : bs')) <- cloneCaseBndrs env dest_lvl (case_bndr : bs)
       ; let rhs_env = extendCaseBndrEnv env1 case_bndr scrut'
       ; body' <- lvlMFE True rhs_env body
       ; let alt' = (con, [TB b (StayPut dest_lvl) | b <- bs'], body')
       ; return (Case scrut' (TB case_bndr' (FloatMe dest_lvl)) ty' [alt']) }

  | otherwise     -- Stays put
  = do { let (alts_env1, [case_bndr']) = substAndLvlBndrs NonRecursive env incd_lvl [case_bndr]
             alts_env = extendCaseBndrEnv alts_env1 case_bndr scrut'
       ; alts' <- mapM (lvl_alt alts_env) alts
       ; return (Case scrut' case_bndr' ty' alts') }
  where
    ty' = substTy (le_subst env) ty

    incd_lvl = incMinorLvl (le_ctxt_lvl env)
    dest_lvl = maxFvLevel (const True) env scrut_fvs
            -- Don't abstact over type variables, hence const True

    lvl_alt alts_env (con, bs, rhs)
      = do { rhs' <- lvlMFE True new_env rhs
           ; return (con, bs', rhs') }
      where
        (new_env, bs') = substAndLvlBndrs NonRecursive alts_env incd_lvl bs

{-
Note [Floating cases]
~~~~~~~~~~~~~~~~~~~~~
Consider this:
  data T a = MkT !a
  f :: T Int -> blah
  f x vs = case x of { MkT y ->
             let f vs = ...(case y of I# w -> e)...f..
             in f vs
Here we can float the (case y ...) out , because y is sure
to be evaluated, to give
  f x vs = case x of { MkT y ->
           caes y of I# w ->
             let f vs = ...(e)...f..
             in f vs

That saves unboxing it every time round the loop.  It's important in
some DPH stuff where we really want to avoid that repeated unboxing in
the inner loop.

Things to note
 * We can't float a case to top level
 * It's worth doing this float even if we don't float
   the case outside a value lambda.  Example
     case x of {
       MkT y -> (case y of I# w2 -> ..., case y of I# w2 -> ...)
   If we floated the cases out we could eliminate one of them.
 * We only do this with a single-alternative case

Note [Check the output scrutinee for okForSpec]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider this:
  case x of y {
    A -> ....(case y of alts)....
  }
Because of the binder-swap, the inner case will get substituted to
(case x of ..).  So when testing whether the scrutinee is
okForSpecuation we must be careful to test the *result* scrutinee ('x'
in this case), not the *input* one 'y'.  The latter *is* ok for
speculation here, but the former is not -- and indeed we can't float
the inner case out, at least not unless x is also evaluated at its
binding site.

That's why we apply exprOkForSpeculation to scrut' and not to scrut.
-}

lvlMFE ::  Bool                 -- True <=> strict context [body of case or let]
        -> LevelEnv             -- Level of in-scope names/tyvars
        -> CoreExprWithBoth     -- input expression
        -> LvlM LevelledExpr    -- Result expression
-- lvlMFE is just like lvlExpr, except that it might let-bind
-- the expression, so that it can itself be floated.

lvlMFE strict_ctxt env (splitAnnCxt -> InNewCxt (TB cid _) expr)
  = do let env' = enterTailContext env cid
           lvl' = le_ctxt_lvl env'
       expr' <- lvlMFE strict_ctxt env' expr
       return (markCxt (TB cid (StayPut lvl')) (idType cid) expr')

lvlMFE _ env (_, AnnType ty)
  = return (Type (substTy (le_subst env) ty))

-- No point in floating out an expression wrapped in a coercion or note
-- If we do we'll transform  lvl = e |> co
--                       to  lvl' = e; lvl = lvl' |> co
-- and then inline lvl.  Better just to float out the payload.
lvlMFE strict_ctxt env (_, AnnTick t e)
  = do { e' <- lvlMFE strict_ctxt env e
       ; return (Tick t e') }

lvlMFE strict_ctxt env (_, AnnCast e (_, co))
  = do  { e' <- lvlMFE strict_ctxt env e
        ; return (Cast e' (substCo (le_subst env) co)) }

-- Note [Case MFEs]
lvlMFE True env e@(_, AnnCase {})
  = lvlExpr env e     -- Don't share cases

lvlMFE strict_ctxt env ann_expr
  |  isFinalPass env
  || floatTopLvlOnly env && not (isTopLvl dest_lvl)
         -- Only floating to the top level is allowed.
  || isTopLvl dest_lvl && need_join -- Can't put join point at top level
  || isUnliftedType (exprType (deTagExpr expr))
         -- Can't let-bind it; see Note [Unlifted MFEs]
         -- This includes coercions, which we don't want to float anyway
         -- NB: no need to substitute cos isUnliftedType doesn't change
  || notWorthFloating ann_expr abs_vars
  || not float_me
  =     -- Don't float it out
    lvlExpr env ann_expr

  | otherwise   -- Float it out!
  = do { expr' <- lvlFloatRhs abs_vars dest_lvl env ann_expr
       ; var   <- newLvlVar expr' is_bot join_arity_maybe
       ; return (Let (NonRec (TB var (FloatMe dest_lvl)) expr')
                     (mkVarApps (Var var) abs_vars)) }
  where
    expr     = deAnnotate ann_expr
    fvs      = fvsOf ann_expr
    is_bot   = exprIsBottom (deTagExpr expr)      -- Note [Bottoming floats]
    dest_lvl = destLevel env fvs (isFunction (deTagExpr expr)) is_bot need_join
    abs_vars = abstractVars dest_lvl env fvs

        -- Note [Join points and MFEs]
    need_join = any (\v -> isId v && remainsJoinId env v) (dVarSetElems fvs)
    join_arity_maybe | need_join = Just (length abs_vars)
                     | otherwise = Nothing

        -- A decision to float entails let-binding this thing, and we only do
        -- that if we'll escape a value lambda, or will go to the top level.
    float_me = dest_lvl `ltMajLvl` (le_ctxt_lvl env)    -- Escapes a value lambda
                -- OLD CODE: not (exprIsCheap expr) || isTopLvl dest_lvl
                --           see Note [Escaping a value lambda]

            || (isTopLvl dest_lvl       -- Only float if we are going to the top level
                && floatConsts env      --   and the floatConsts flag is on
                && not strict_ctxt)     -- Don't float from a strict context
          -- We are keen to float something to the top level, even if it does not
          -- escape a lambda, because then it needs no allocation.  But it's controlled
          -- by a flag, because doing this too early loses opportunities for RULES
          -- which (needless to say) are important in some nofib programs
          -- (gcd is an example).
          --
          -- Beware:
          --    concat = /\ a -> foldr ..a.. (++) []
          -- was getting turned into
          --    lvl    = /\ a -> foldr ..a.. (++) []
          --    concat = /\ a -> lvl a
          -- which is pretty stupid.  Hence the strict_ctxt test
          --
          -- Also a strict contxt includes uboxed values, and they
          -- can't be bound at top level

{-
Note [Unlifted MFEs]
~~~~~~~~~~~~~~~~~~~~
We don't float unlifted MFEs, which potentially loses big opportunites.
For example:
        \x -> f (h y)
where h :: Int -> Int# is expensive. We'd like to float the (h y) outside
the \x, but we don't because it's unboxed.  Possible solution: box it.

Note [Bottoming floats]
~~~~~~~~~~~~~~~~~~~~~~~
If we see
        f = \x. g (error "urk")
we'd like to float the call to error, to get
        lvl = error "urk"
        f = \x. g lvl
Furthermore, we want to float a bottoming expression even if it has free
variables:
        f = \x. g (let v = h x in error ("urk" ++ v))
Then we'd like to abstact over 'x' can float the whole arg of g:
        lvl = \x. let v = h x in error ("urk" ++ v)
        f = \x. g (lvl x)
See Maessen's paper 1999 "Bottom extraction: factoring error handling out
of functional programs" (unpublished I think).

When we do this, we set the strictness and arity of the new bottoming
Id, *immediately*, for three reasons:

  * To prevent the abstracted thing being immediately inlined back in again
    via preInlineUnconditionally.  The latter has a test for bottoming Ids
    to stop inlining them, so we'd better make sure it *is* a bottoming Id!

  * So that it's properly exposed as such in the interface file, even if
    this is all happening after strictness analysis.

  * In case we do CSE with the same expression that *is* marked bottom
        lvl          = error "urk"
          x{str=bot) = error "urk"
    Here we don't want to replace 'x' with 'lvl', else we may get Lint
    errors, e.g. via a case with empty alternatives:  (case x of {})
    Lint complains unless the scrutinee of such a case is clearly bottom.

    This was reported in Trac #11290.   But since the whole bottoming-float
    thing is based on the cheap-and-cheerful exprIsBottom, I'm not sure
    that it'll nail all such cases.

Note [Bottoming floats: eta expansion] c.f Note [Bottoming floats]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Tiresomely, though, the simplifier has an invariant that the manifest
arity of the RHS should be the same as the arity; but we can't call
etaExpand during SetLevels because it works over a decorated form of
CoreExpr.  So we do the eta expansion later, in FloatOut.

Note [Case MFEs]
~~~~~~~~~~~~~~~~
We don't float a case expression as an MFE from a strict context.  Why not?
Because in doing so we share a tiny bit of computation (the switch) but
in exchange we build a thunk, which is bad.  This case reduces allocation
by 7% in spectral/puzzle (a rather strange benchmark) and 1.2% in real/fem.
Doesn't change any other allocation at all.

Note [Join points and MFEs]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

When we create an MFE float, if it has a free join variable, the new binding
must be a join point:

  let join j x = ...
  in case a of A -> ...
               B -> j 3

  =>

  let join j x = ...
      join k = j 3 -- only valid because k is a join point
  in case a of A -> ...
               B -> k

Normally we're very circumspect about floating join points, but in this case
it's definitely safe because we can only be floating it as far as another join
binding. In other words, one might worry about a situation like:

  let join j x = ...
  in case a of A -> ...
               B -> f (j 3)

  =>

  let join j x = ...
  in case a of A -> ...
               B -> f (let join k = j 3 in k)

Here we have created the MFE float k, and are contemplating floating it up to
j. This would indeed be an invalid operation on a join point like k. However,
this example is ill-typed to begin with, since this time the call to j is not a
tail call. In summary, the very occurrence of the join variable in the MFE is
proof that we can float the MFE as far as that binding.
-}

annotateBotStr :: Id -> Maybe (Arity, StrictSig) -> Id
-- See Note [Bottoming floats] for why we want to add
-- bottoming information right now
annotateBotStr id Nothing            = id
annotateBotStr id (Just (arity, sig)) = id `setIdArity` arity
                                           `setIdStrictness` sig

notWorthFloating :: CoreExprWithBoth -> [Var] -> Bool
-- Returns True if the expression would be replaced by
-- something bigger than it is now.  For example:
--   abs_vars = tvars only:  return True if e is trivial,
--                           but False for anything bigger
--   abs_vars = [x] (an Id): return True for trivial, or an application (f x)
--                           but False for (f x x)
--
-- One big goal is that floating should be idempotent.  Eg if
-- we replace e with (lvl79 x y) and then run FloatOut again, don't want
-- to replace (lvl79 x y) with (lvl83 x y)!

notWorthFloating e abs_vars
  = go e (count isId abs_vars)
  where
    go (_, AnnVar {}) n    = n >= 0
    go (_, AnnLit lit) n   = ASSERT( n==0 )
                             litIsTrivial lit   -- Note [Floating literals]
    go (_, AnnTick t e) n  = not (tickishIsCode t) && go e n
    go (_, AnnCast e _)  n = go e n
    go (_, AnnApp e arg) n
       | (_, AnnType {}) <- arg = go e n
       | (_, AnnCoercion {}) <- arg = go e n
       | n==0                   = False
       | is_triv arg            = go e (n-1)
       | otherwise              = False
    go _ _                      = False

    is_triv (_, AnnLit {})                = True        -- Treat all literals as trivial
    is_triv (_, AnnVar {})                = True        -- (ie not worth floating)
    is_triv (_, AnnCast e _)              = is_triv e
    is_triv (_, AnnApp e (_, AnnType {})) = is_triv e
    is_triv (_, AnnApp e (_, AnnCoercion {})) = is_triv e
    is_triv (_, AnnTick t e)              = not (tickishIsCode t) && is_triv e
    is_triv _                             = False

{-
Note [Floating literals]
~~~~~~~~~~~~~~~~~~~~~~~~
It's important to float Integer literals, so that they get shared,
rather than being allocated every time round the loop.
Hence the litIsTrivial.

We'd *like* to share MachStr literal strings too, mainly so we could
CSE them, but alas can't do so directly because they are unlifted.


Note [Escaping a value lambda]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We want to float even cheap expressions out of value lambdas,
because that saves allocation.  Consider
        f = \x.  .. (\y.e) ...
Then we'd like to avoid allocating the (\y.e) every time we call f,
(assuming e does not mention x).

An example where this really makes a difference is simplrun009.

Another reason it's good is because it makes SpecContr fire on functions.
Consider
        f = \x. ....(f (\y.e))....
After floating we get
        lvl = \y.e
        f = \x. ....(f lvl)...
and that is much easier for SpecConstr to generate a robust specialisation for.

The OLD CODE (given where this Note is referred to) prevents floating
of the example above, so I just don't understand the old code.  I
don't understand the old comment either (which appears below).  I
measured the effect on nofib of changing OLD CODE to 'True', and got
zeros everywhere, but a 4% win for 'puzzle'.  Very small 0.5% loss for
'cse'; turns out to be because our arity analysis isn't good enough
yet (mentioned in Simon-nofib-notes).

OLD comment was:
         Even if it escapes a value lambda, we only
         float if it's not cheap (unless it'll get all the
         way to the top).  I've seen cases where we
         float dozens of tiny free expressions, which cost
         more to allocate than to evaluate.
         NB: exprIsCheap is also true of bottom expressions, which
             is good; we don't want to share them

        It's only Really Bad to float a cheap expression out of a
        strict context, because that builds a thunk that otherwise
        would never be built.  So another alternative would be to
        add
                || (strict_ctxt && not (exprIsBottom expr))
        to the condition above. We should really try this out.

Node [Lifting LNEs]
~~~~~~~~~~~~~~~~~~~

Lifting LNEs is dubious. The only benefit of lifting an LNE is the
reduction in expression size increasing the likelihood of inlining,
eg. LNEs do not allocate and by definition cannot pin other function
closures.

However a function call seems to be a bit slower than an LNE entry;
TODO investigate the CMM difference.

************************************************************************
*                                                                      *
\subsection{Bindings}
*                                                                      *
************************************************************************

The binding stuff works for top level too.
-}

unTag :: TaggedBndr b -> CoreBndr
unTag (TB b _) = b

lvlBind :: LevelEnv
        -> CoreBindWithBoth
        -> LvlM (LevelledBind, LevelEnv)

lvlBind env binding@(AnnNonRec bndr rhs)
  = case decideBindFloat env (exprIsBottom $ deTagExpr $ deAnnotate rhs) binding of
      Nothing -> do
        { rhs' <- lvlRhs env NonRecursive bndr rhs
        ; let  bind_lvl        = incMinorLvl (le_ctxt_lvl env)
               (env', [bndr']) = substAndLvlBndrs NonRecursive env bind_lvl [bndr]
        ; return (NonRec bndr' rhs', env') }

      Just (dest_lvl, abs_vars, zapping_join)
        | null abs_vars
        -> do {  -- No type abstraction; clone existing binder
                rhs' <- lvlExpr (setCtxtLvl env dest_lvl) rhs
              ; (env', [bndr']) <- cloneLetVars NonRecursive env
                                                dest_lvl zapping_join [bndr]
              ; return (NonRec (TB bndr' (FloatMe dest_lvl)) rhs', env') }
        | otherwise
        -> do {  -- Yes, type abstraction; create a new binder, extend substitution, etc
                rhs' <- lvlFloatRhs abs_vars dest_lvl env rhs
              ; (env', [bndr']) <- newPolyBndrs dest_lvl env abs_vars
                                                zapping_join [bndr]
              ; return (NonRec (TB bndr' (FloatMe dest_lvl)) rhs', env') }

lvlBind env binding@(AnnRec pairs)
  = case decideBindFloat env False binding of
      Nothing -> do -- decided to not float
        { let bind_lvl = incMinorLvl (le_ctxt_lvl env)
              (env', bndrs') = substAndLvlBndrs Recursive env bind_lvl bndrs
        ; rhss' <- Control.Monad.zipWithM (lvlRhs env' Recursive) bndrs rhss
        ; return (Rec (bndrs' `zip` rhss'), env')
        }

      Just (dest_lvl, abs_vars, zapping_joins) -- decided to float
        | null abs_vars -> do
        { (new_env, new_bndrs) <- cloneLetVars Recursive env
                                               dest_lvl zapping_joins bndrs
        ; new_rhss <- mapM (lvlExpr (setCtxtLvl new_env dest_lvl)) rhss
        ; return ( Rec ([TB b (FloatMe dest_lvl) | b <- new_bndrs] `zip` new_rhss)
                 , new_env
                 )
        }

        | otherwise -> do  -- Non-null abs_vars
        { (new_env, new_bndrs) <- newPolyBndrs dest_lvl env
                                               abs_vars zapping_joins bndrs
        ; new_rhss <- mapM (lvlFloatRhs abs_vars dest_lvl new_env) rhss
        ; return ( Rec ([TB b (FloatMe dest_lvl) | b <- new_bndrs] `zip` new_rhss)
                 , new_env
          )
        }
  where
    (bndrs, rhss) = unzip pairs

-- Only used when NOT floating, since floating will promote the join point to a
-- function (see Note [When to ruin a join point]).
lvlRhs :: LevelEnv
       -> RecFlag
       -> TaggedBndr BSilt
       -> CoreExprWithBoth
       -> LvlM LevelledExpr
lvlRhs env rec_flag (TB bndr _) expr
  | Just join_arity <- isJoinId_maybe bndr
  = do { let (bndrs, body)            = collectNAnnBndrs join_arity expr
             new_lvl | isRec rec_flag = incMajorLvl (le_ctxt_lvl env)
                     | otherwise      = incMinorLvl (le_ctxt_lvl env)
               -- Non-recursive joins are one-shot; recursive joins are not
             (env1, bndrs1)           = substBndrsSL NonRecursive env bndrs
             (new_env, new_bndrs)     = lvlBndrs env1 new_lvl bndrs1
       ; new_body <- lvlExpr new_env body
       ; return (mkLams new_bndrs new_body) }

lvlRhs env _ _ expr
  = lvlExpr env expr

decideBindFloat ::
  LevelEnv ->
  Bool -> -- is it a bottoming non-rec RHS?
  CoreBindWithBoth ->
  Maybe (Level,[Var],Bool) -- Nothing <=> do not float
                           --
                           -- Just (lvl, vs) <=> float to lvl using vs as
                           -- the abs_vars
                           --
                           -- True <=> zap the join points in the float
                           -- (promote them to values)
decideBindFloat _ _ (AnnNonRec (TB bndr _) _)
  | isTyVar bndr    -- Don't do anything for TyVar binders
                    --   (simplifier gets rid of them pronto)
  || isCoVar bndr   -- Difficult to fix up CoVar occurrences (see extendPolyLvlEnv)
                    -- so we will ignore this case for now
  = Nothing

decideBindFloat init_env is_bot binding =
  maybe conventionalFloatOut lateLambdaLift (finalPass env)
  where
    env = lneLvlEnv init_env ids
    conventionalFloatOut | is_forbidden_float  = Nothing
                         | is_profitable_float = Just (dest_lvl, abs_vars,
                                                       zapping_joins)
                         | otherwise         = Nothing
      where
        dest_lvl = destLevel env bindings_fvs all_funs is_bot
                             has_unfloatable_join_binding

        abs_vars = abstractVars dest_lvl env bindings_fvs

        is_forbidden_float =
             (isTopLvl dest_lvl && is_unlifted_binding)
               -- We can't float an unlifted binding to top level, so we don't
               -- float it at all.  It's a bit brutal, but unlifted bindings
               -- aren't expensive either
          || floatTopLvlOnly env && not (isTopLvl dest_lvl)
               -- Note [When to ruin a join point]

        is_profitable_float =
             (dest_lvl `ltMajLvl` le_ctxt_lvl init_env) -- Escapes a value lambda
          || isTopLvl dest_lvl -- Going all the way to top level

        is_unlifted_binding
          = case binding of
              AnnNonRec (TB bndr _) _ -> isUnliftedType (idType bndr)
              _                       -> False

        has_unfloatable_join_binding =
          any (\(TB bndr _) -> case isJoinId_maybe bndr of Just ar -> ar > 0
                                                           Nothing -> False)
              ids
            -- See [When to ruin a join point]

        zapping_joins = dest_lvl `ltLvl` joinCeilingLevel init_env

    lateLambdaLift fps
      | all_funs || (fps_floatLNE0 fps && isLNE)
           -- only lift functions or zero-arity LNEs
      ,  not (any (`elemVarSet` le_joins env) abs_vars) -- can't abstract over join
      ,  not (fps_leaveLNE fps && isLNE) -- see Note [Lifting LNEs]
      ,  Nothing <- decider = Just (tOP_LEVEL, abs_vars, True)
      | otherwise = Nothing -- do not lift
      where
        abs_vars = abstractVars tOP_LEVEL env bindings_fvs
        abs_ids_set = expandFloatedIds env $ mapDVarEnv fii_var bindings_fiis
        abs_ids  = dVarSetElems abs_ids_set

        decider = decideLateLambdaFloat env isRec isLNE all_one_shot abs_ids_set badTime spaceInfo ids extra_sdoc fps

        badTime   = wouldIncreaseRuntime    env abs_ids bindings_fiis
        spaceInfo = wouldIncreaseAllocation env isLNE abs_ids_set rhs_silt_s scope_silt

        -- for -ddump-late-float with -dppr-debug
        extra_sdoc = text "scope_silt:" <+> ppr scope_silt
                  $$ text "le_env env:" <+> ppr (le_env env)
                  $$ text "abs_vars:"   <+> ppr abs_vars

    isRec        = case binding of AnnNonRec {} -> False
                                   AnnRec {}    -> True
    pairs        = case binding of AnnNonRec id rhs -> [(id, rhs)]
                                   AnnRec pairs     -> pairs
    (ids, rhss)  = unzip pairs
    rhs_silt_s   = [(unTag id, siltOf rhs) | (id, rhs) <- pairs]
    TB b bsilt   = head ids
    join_arity   = isJoinId_maybe b
      -- in a recursive group, the binder sort and the scope silt are the same
      -- for each
    scope_silt   = case bsilt of BoringB -> emptySilt
                                 CloB scope -> scope
    all_funs     = all (isFunction . deTagExpr . deAnnotate) rhss
    all_one_shot = all is_OneShot rhss
    (bindings_fvs, bindings_fiis)
      = case binding of
          AnnNonRec (TB bndr _) rhs ->
            (fvsOf rhs `unionDVarSet` dIdFreeVars bndr, siltFIIs (siltOf rhs))
          AnnRec _ ->
            (delBindersFVs (map unTag ids) rhss_fvs, siltFIIs $ delBindersSilt (map unTag ids) rhss_silt)
            where
              rhss_silt = foldr bothSilt emptySilt (map siltOf rhss)
              rhss_fvs  = computeRecRHSsFVs (map unTag ids) (map fvsOf rhss)

    isLNE = isJust join_arity
    is_OneShot e = case collectBinders $ deTagExpr $ deAnnotate e of
      (bs,_) -> all (\b -> isId b && isOneShotBndr b) bs

{-
Note [When to ruin a join point]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Generally, we protect join points zealously. However, there are two situations
in which it can pay to promote a join point to a function:

1. If the join point has no value arguments, then floating it outward will make
   it a *thunk*, not a function, so we might get increased sharing.
2. If we float the join point all the way to the top level, it still won't be
   allocated, so the cost is much less.

Refusing to lose a join point in either of these cases can be disastrous---for
instance, allocation in imaginary/x2n1 *triples* because $w$s^ becomes too big
to inline, which prevents Float In from making a particular binding strictly
demanded.
-}

decideLateLambdaFloat ::
  LevelEnv ->
  Bool ->
  Bool ->
  Bool ->
  DIdSet ->
  DIdSet -> [(Bool, WordOff, WordOff, WordOff)] ->
  [InId] -> SDoc ->
  FinalPassSwitches ->
  Maybe DVarSet -- Nothing <=> float to tOP_LEVEL
                --
                -- Just x <=> do not float, not (null x) <=> forgetting
                -- fast calls to the ids in x are the only thing
                -- pinning this binding
decideLateLambdaFloat env isRec isLNE all_one_shot abs_ids_set badTime spaceInfo ids extra_sdoc fps
  = (if fps_trace fps then pprTrace ('\n' : msg) msg_sdoc else (\x -> x)) $
    if floating then Nothing else Just $
    if isBadSpace
    then emptyDVarSet -- do not float, ever
    else badTime
         -- not floating, in order to not abstract over these
  where
    floating = not $ isBadTime || isBadSpace

    msg = (if floating then "late-float" else "late-no-float")
          ++ (if isRec then "(rec " ++ show (length ids) ++ ")" else "")
          ++ if floating && isBadSpace then "(SAT)" else ""

    isBadTime = not (isEmptyDVarSet badTime)

    -- this should always be empty, by definition of LNE
    spoiledLNEs = le_joins env `intersectVarSet` mkVarSet (dVarSetElems abs_ids_set)

    isBadSpace | fps_oneShot fps && all_one_shot = False
               | otherwise    = flip any spaceInfo $ \(createsPAPs, cloSize, cg, cgil) ->
      papViolation createsPAPs || cgViolation (cg - cloSize) || cgilViolation cgil

    papViolation x | fps_createPAPs fps = False
                   | otherwise = x

    cgViolation = case fps_cloGrowth fps of
      Nothing -> const False
      Just limit -> (> limit * wORDS_PTR)

      -- If the closure is NOT under a lambda, then we get a discount
      -- for no longer allocating these bindings' closures, since
      -- these bindings would be allocated at least as many times as
      -- the closure.

    cgilViolation = case fps_cloGrowthInLam fps of
      Nothing -> const False
      Just limit -> (> limit * wORDS_PTR)

      -- If the closure is under a lambda, we do NOT discount for not
      -- allocating these bindings' closures, since the closure could
      -- be allocated many more times than these bindings are.

    msg_sdoc = vcat (zipWith space (map unTag ids) spaceInfo) where
      abs_ids = dVarSetElems abs_ids_set
      space v (badPAP, closureSize, cg, cgil) = vcat
       [ ppr v <+> if isLNE then parens (text "LNE") else empty
       , text "size:" <+> ppr closureSize
       , text "abs_ids:" <+> ppr (length abs_ids) <+> ppr abs_ids
       , text "createsPAPs:" <+> ppr badPAP
       , text "closureGrowth:" <+> ppr cg
       , text "CG in lam:"   <+> ppr cgil
       , text "fast-calls:" <+> ppr (dVarSetElems badTime)
       , if isEmptyVarSet spoiledLNEs then empty else text "spoiledLNEs!!:" <+> ppr spoiledLNEs
       , if opt_PprStyle_Debug then extra_sdoc else empty
       ]

    wORDS_PTR = StgCmmArgRep.argRepSizeW (le_dflags env) StgCmmArgRep.P

-- see Note [Preserving Fast Entries]
wouldIncreaseRuntime ::
  LevelEnv ->
  [Id] ->      -- the abstracted value ids
  FIIs ->      -- FIIs for the bindings' RHS
  DVarSet      -- the forgotten ids
wouldIncreaseRuntime env abs_ids binding_group_fiis = case prjFlags `fmap` finalPass env of
  -- is final pass...
  Just (noUnder, noExact, noOver) | noUnder || noExact || noOver ->
    mkDVarSet $ flip mapMaybe abs_ids $ \abs_id ->
      case lookupDVarEnv binding_group_fiis abs_id of
        Just fii | idArity abs_id > 0, -- NB (arity > 0) iff "is known function"
                   under||exact||over, -- is applied
                      (noUnder && under)
                   || (noExact && exact)
                   || (noOver  && over)
                 -> Just abs_id
          where (_unapplied,under,exact,over) = fii_useInfo fii
        _ -> Nothing
  _ -> emptyDVarSet
  where prjFlags fps = ( not (fps_absUnsatVar   fps) -- -fno-late-abstract-undersat-var
                       , not (fps_absSatVar     fps) -- -fno-late-abstract-sat-var
                       , not (fps_absOversatVar fps) -- -fno-late-abstract-oversat-var
                       )

-- if a free id was floated, then its abs_ids are now free ids
expandFloatedIds :: LevelEnv -> {- In -} DIdSet -> {- Out -} DIdSet
expandFloatedIds env = foldl snoc emptyDVarSet . dVarSetElems where
  snoc acc id = case lookupVarEnv (le_env env) id of
    Nothing -> extendDVarSet acc id -- TODO is this case possible?
    Just (new_id,filter isId -> abs_ids)
      | not (null abs_ids) -> -- it's a lambda-lifted function
                              extendDVarSetList acc abs_ids
      | otherwise          -> extendDVarSet     acc new_id

wouldIncreaseAllocation ::
  LevelEnv ->
  Bool ->
  DIdSet ->      -- the abstracted value ids
  [(Id, FISilt)] -> -- the bindings in the binding group with each's
                    -- silt
  FISilt ->       -- the entire scope of the binding group
  [] -- for each binder:
    ( Bool -- would create PAPs
    , WordOff  -- size of this closure group
    , WordOff  -- estimated increase for closures that are NOT
               -- allocated under a lambda
    , WordOff  -- estimated increase for closures that ARE allocated
               -- under a lambda
    )
wouldIncreaseAllocation env isLNE abs_ids_set pairs (FISilt _ scope_fiis scope_sk)
  | isLNE = map (const (False,0,0,0)) pairs
  | otherwise = flip map bndrs $ \bndr -> case lookupDVarEnv scope_fiis bndr of
    Nothing -> (False, closuresSize, 0, 0) -- it's a dead variable. Huh.
    Just fii -> (violatesPAPs, closuresSize, closureGrowth, closureGrowthInLambda)
      where
        violatesPAPs = let (unapplied,_,_,_) = fii_useInfo fii in unapplied

        (closureGrowth, closureGrowthInLambda)
          = costToLift (expandFloatedIds env) sizer bndr abs_ids_set scope_sk
    where
      bndrs = map fst pairs

      dflags = le_dflags env

      -- It's not enough to calculate "total size of abs_ids" because
      -- each binding in a letrec may have incomparable sets of free
      -- ids. abs_ids is merely the union of those sets.
      --
      -- So we instead calculate and then add up the size of each
      -- binding's closure. GHC does not currently share closure
      -- environments, and we either lift the entire recursive binding
      -- group or none of it.
      closuresSize = sum $ flip map pairs $ \(_,FISilt _ fiis _) ->
        let (words, _, _) =
              StgCmmLayout.mkVirtHeapOffsets dflags isUpdateable $
              StgCmmClosure.addIdReps $
              filter (`elemDVarSet` abs_ids_set) $
              dVarEnvElts $ expandFloatedIds env $ -- NB In versus Out ids
              mapDVarEnv fii_var fiis
              where isUpdateable = False -- functions are not updateable
        in words + sTD_HDR_SIZE dflags -- ignoring profiling overhead
           -- safely ignoring the silt's satTypes; should always be []
           -- because this is a *function* closure we're considering

      sizer :: Id -> WordOff
      sizer = argRep_sizer . toArgRep . StgCmmClosure.idPrimRep

      argRep_sizer :: ArgRep -> WordOff
      argRep_sizer = StgCmmArgRep.argRepSizeW dflags

----------------------------------------------------
-- Three help functions for the type-abstraction case

lvlFloatRhs :: [OutVar] -> Level -> LevelEnv -> CoreExprWithBoth
            -> LvlM (Expr LevelledBndr)
lvlFloatRhs abs_vars dest_lvl env rhs
  = do { rhs' <- lvlExpr rhs_env rhs
       ; return (mkLams abs_vars_w_lvls rhs') }
  where
    (rhs_env, abs_vars_w_lvls) = lvlLamBndrs env dest_lvl abs_vars

{-
************************************************************************
*                                                                      *
\subsection{Deciding floatability}
*                                                                      *
************************************************************************
-}

substAndLvlBndrs :: RecFlag -> LevelEnv -> Level -> [TaggedBndr BSilt] -> (LevelEnv, [LevelledBndr])
substAndLvlBndrs is_rec env lvl bndrs
  = lvlBndrs subst_env lvl subst_bndrs
  where
    (subst_env, subst_bndrs) = substBndrsSL is_rec env bndrs

substBndrsSL :: RecFlag -> LevelEnv -> [TaggedBndr BSilt] -> (LevelEnv, [OutVar])
-- So named only to avoid the name clash with CoreSubst.substBndrs
substBndrsSL is_rec env@(LE { le_subst = subst, le_env = id_env, le_joins = joins }) bndrs
  = ( env { le_subst    = subst'
          , le_env      = foldl add_id  id_env (bndrs `zip` bndrs')
          , le_joins    = extendVarSetList joins [ bndr | TB bndr _ <- bndrs
                                                        , isId bndr, isJoinId bndr ]}
    , bndrs')
  where
    (subst', bndrs') = case is_rec of
                         NonRecursive -> substBndrs    subst (map unTag bndrs)
                         Recursive    -> substRecBndrs subst (map unTag bndrs)

lvlLamBndrs :: LevelEnv -> Level -> [OutVar] -> (LevelEnv, [LevelledBndr])
-- Compute the levels for the binders of a lambda group
lvlLamBndrs env lvl bndrs
  = lvlBndrs env new_lvl bndrs
  where
    new_lvl | any is_major bndrs = incMajorLvl lvl
            | otherwise          = incMinorLvl lvl

    is_major bndr = isId bndr && not (isProbablyOneShotLambda bndr)
       -- The "probably" part says "don't float things out of a
       -- probable one-shot lambda"
       -- See Note [Computing one-shot info] in Demand.hs


lvlBndrs :: LevelEnv -> Level -> [CoreBndr] -> (LevelEnv, [LevelledBndr])
-- The binders returned are exactly the same as the ones passed,
-- apart from applying the substitution, but they are now paired
-- with a (StayPut level)
--
-- The returned envt has le_ctxt_lvl updated to the new_lvl
--
-- All the new binders get the same level, because
-- any floating binding is either going to float past
-- all or none.  We never separate binders.
lvlBndrs env@(LE { le_lvl_env = lvl_env }) new_lvl bndrs
  = ( env { le_ctxt_lvl = new_lvl
          , le_lvl_env  = addLvls new_lvl lvl_env bndrs }
    , lvld_bndrs)
  where
    lvld_bndrs    = [TB bndr (StayPut new_lvl) | bndr <- bndrs]

  -- Destination level is the max Id level of the expression
  -- (We'll abstract the type variables, if any.)
destLevel :: LevelEnv -> DVarSet
          -> Bool   -- True <=> is function
          -> Bool   -- True <=> is bottom
          -> Bool   -- True <=> is join point
          -> Level
destLevel env fvs _is_function is_bot is_join
  | is_bot = tOP_LEVEL  -- Send bottoming bindings to the top
                        -- regardless; see Note [Bottoming floats]
  | is_join, hits_ceiling = join_ceiling
  | otherwise = max_fv_level
  where
    max_fv_level = maxFvLevel isId env fvs -- Max over Ids only; the tyvars
                                           -- will be abstracted

    hits_ceiling = max_fv_level `ltLvl` join_ceiling &&
                   not (isTopLvl max_fv_level) -- Note [When to ruin a join point]
    join_ceiling = joinCeilingLevel env

isFunction :: CoreExpr -> Bool
isFunction (Lam b e) | isId b = True
                     | otherwise = isFunction e
-- isFunction (_, AnnTick _ e)          = isFunction e  -- dubious
isFunction _                           = False

{-
************************************************************************
*                                                                      *
\subsection{Free-To-Level Monad}
*                                                                      *
************************************************************************
-}

type InVar  = TaggedBndr BSilt -- Pre  cloning
type InId   = TaggedBndr BSilt -- Pre  cloning
type OutVar = Var          -- Post cloning
type OutId  = Id           -- Post cloning

data LevelEnv
  = LE { le_switches :: FloatOutSwitches
       , le_ctxt_lvl :: Level           -- The current level
       , le_lvl_env  :: VarEnv Level    -- Domain is *post-cloned* TyVars and Ids
       , le_cid      :: CxtId           -- Identifier for tail context (see CoreCxts)
       , le_subst    :: Subst           -- Domain is pre-cloned TyVars and Ids
                                        -- The Id -> CoreExpr in the Subst is ignored
                                        -- (since we want to substitute in LevelledExpr
                                        -- instead) but we do use the Co/TyVar substs
       , le_env      :: IdEnv (OutVar,[OutVar]) -- Domain is pre-cloned Ids
           -- (v,vs) represents the application "v vs0 vs1 vs2" ...
           -- Except in the late float, the vs are all types.

        -- see Note [The Reason SetLevels Does Substitution]

       , le_dflags   :: DynFlags
       , le_joins    :: VarSet
    }
        -- We clone let- and case-bound variables so that they are still
        -- distinct when floated out; hence the le_subst/le_env.
        -- (see point 3 of the module overview comment).
        -- We also use these envs when making a variable polymorphic
        -- because we want to float it out past a big lambda.
        --
        -- The le_subst and le_env always implement the same mapping, but the
        -- le_subst maps to CoreExpr and the le_env to LevelledExpr
        -- Since the range is always a variable or type application,
        -- there is never any difference between the two, but sadly
        -- the types differ.  The le_subst is used when substituting in
        -- a variable's IdInfo; the le_env when we find a Var.
        --
        -- In addition the le_env representation caches the free
        -- tyvars range, just so we don't have to call freeVars on the
        -- type application repeatedly.
        --
        -- The domain of the both envs is *pre-cloned* Ids, though
        --
        -- The domain of the le_lvl_env is the *post-cloned* Ids

initialEnv :: DynFlags -> FloatOutSwitches -> LevelEnv
initialEnv dflags float_lams
  = LE { le_switches = float_lams
       , le_ctxt_lvl = tOP_LEVEL
       , le_cid = panic "initialEnv"
       , le_lvl_env = emptyVarEnv
       , le_subst = emptySubst
       , le_env = emptyVarEnv
       , le_dflags = dflags
       , le_joins = emptyVarSet }

addLvl :: Level -> VarEnv Level -> OutVar -> VarEnv Level
addLvl dest_lvl env v' = extendVarEnv env v' dest_lvl

addLvls :: Level -> VarEnv Level -> [OutVar] -> VarEnv Level
addLvls dest_lvl env vs = foldl (addLvl dest_lvl) env vs

finalPass :: LevelEnv -> Maybe FinalPassSwitches
finalPass le = finalPass_ (le_switches le)

isFinalPass :: LevelEnv -> Bool
isFinalPass le = case finalPass le of
  Nothing -> False
  Just _  -> True

floatConsts :: LevelEnv -> Bool
floatConsts le = floatOutConstants (le_switches le)

floatOverSat :: LevelEnv -> Bool
floatOverSat le = floatOutOverSatApps (le_switches le)

floatTopLvlOnly :: LevelEnv -> Bool
floatTopLvlOnly le = floatToTopLevelOnly (le_switches le)

lneLvlEnv :: LevelEnv -> [InId] -> LevelEnv
lneLvlEnv env bndrs = env { le_joins = extendVarSetList (le_joins env) joins }
  where
    joins = [ bndr | TB bndr _ <- bndrs, isJoinId bndr ]

setCtxtLvl :: LevelEnv -> Level -> LevelEnv
setCtxtLvl env lvl = env { le_ctxt_lvl = lvl }

-- extendCaseBndrEnv adds the mapping case-bndr->scrut-var if it can
-- See Note [Binder-swap during float-out]
extendCaseBndrEnv :: LevelEnv
                  -> InId               -- Pre-cloned case binder
                  -> Expr LevelledBndr  -- Post-cloned scrutinee
                  -> LevelEnv
extendCaseBndrEnv le@(LE { le_subst = subst, le_env = id_env })
                  case_bndr (Var scrut_var)
  = le { le_subst   = extendSubstWithVar subst (unTag case_bndr) scrut_var
       , le_env     = add_id id_env (case_bndr, scrut_var) }
extendCaseBndrEnv env _ _ = env

enterTailContext :: LevelEnv -> CxtId -> LevelEnv
enterTailContext le@(LE { le_ctxt_lvl = lvl, le_lvl_env = env }) cid
  = le { le_ctxt_lvl = lvl', le_lvl_env = addLvl lvl' env cid, le_cid = cid }
  where
    lvl' = incMinorLvl lvl

maxFvLevel :: (Var -> Bool) -> LevelEnv -> DVarSet -> Level
maxFvLevel max_me (LE { le_lvl_env = lvl_env, le_env = id_env }) var_set
  = foldDVarSet max_in tOP_LEVEL var_set
  where
    max_in in_var lvl
       = foldr max_out lvl (case lookupVarEnv id_env in_var of
                                Just (v,abs_vars) -> v:abs_vars
                                Nothing            -> [in_var])

    max_out out_var lvl
        | max_me out_var = case lookupVarEnv lvl_env out_var of
                                Just lvl' -> maxLvl lvl' lvl
                                Nothing   -> lvl
        | otherwise = lvl       -- Ignore some vars depending on max_me

lookupVar :: LevelEnv -> Id -> LevelledExpr
lookupVar le v = case lookupVarEnv (le_env le) v of
                    Just (v', vs') -> mkVarApps (Var v') vs'
                    _              -> Var v

-- Level to which join points are allowed to float (boundary of current tail
-- context; would call this "tailContextLevel" but "context" is overloaded here)
joinCeilingLevel :: LevelEnv -> Level
joinCeilingLevel (LE { le_lvl_env = lvl_env, le_cid = cid })
  = case lookupVarEnv lvl_env cid of
      Just lvl -> lvl
      Nothing  -> pprPanic "joinCeilingLevel" (ppr cid)

remainsJoinId :: LevelEnv -> Id -> Bool
remainsJoinId le v = case lookupVarEnv (le_env le) v of
                         Just (v', _) -> isJoinId v'
                         Nothing      -> isJoinId v

abstractVars :: Level -> LevelEnv -> DVarSet -> [OutVar]
        -- Find the variables in fvs, free vars of the target expresion,
        -- whose level is greater than the destination level
        -- These are the ones we are going to abstract out
        --
        -- Note that to get reproducible builds, the variables need to be
        -- abstracted in deterministic order, not dependent on the values of
        -- Uniques. This is achieved by using DVarSets, deterministic free
        -- variable computation and deterministic sort.
        -- See Note [Unique Determinism] in Unique for explanation of why
        -- Uniques are not deterministic.
abstractVars dest_lvl (LE { le_subst = subst, le_lvl_env = lvl_env }) in_fvs
  =  -- NB: sortQuantVars might not put duplicates next to each other
    map zap $ sortQuantVars $ uniq
    [out_var | out_fv  <- dVarSetElems (substDVarSet subst in_fvs)
             , out_var <- dVarSetElems (close out_fv)
             , abstract_me out_var ]
        -- NB: it's important to call abstract_me only on the OutIds the
        -- come from substDVarSet (not on fv, which is an InId)
  where
    uniq :: [Var] -> [Var]
        -- Remove duplicates, preserving order
    uniq = dVarSetElems . mkDVarSet

    abstract_me v = case lookupVarEnv lvl_env v of
                        Just lvl -> dest_lvl `ltLvl` lvl
                        Nothing  -> False

        -- We are going to lambda-abstract, so nuke any IdInfo,
        -- and add the tyvars of the Id (if necessary)
    zap v | isId v = WARN( isStableUnfolding (idUnfolding v) ||
                           not (isEmptyRuleInfo (idSpecialisation v)),
                           text "absVarsOf: discarding info on" <+> ppr v )
                     setIdInfo v vanillaIdInfo
          | otherwise = v

    close :: Var -> DVarSet  -- Close over variables free in the type
                             -- Result includes the input variable itself
    close v = foldDVarSet (unionDVarSet . close)
                          (unitDVarSet v)
                          (fvDVarSet $ varTypeTyCoFVs v)

type PinnedLBFs = VarEnv (Id, VarSet) -- (g, fs, hs) <=> pinned by fs, captured by hs

newtype LvlM a = LvlM (UniqSM (a, PinnedLBFs))
instance Functor LvlM where fmap = Control.Monad.liftM
instance Applicative LvlM where
  pure a = LvlM $ return (a, emptyVarEnv)
  (<*>) = Control.Monad.ap
instance Monad LvlM where
  return = pure
  LvlM m >>= k = LvlM $ m >>= \ ~(a, w) ->
    case k a of
      LvlM m -> m >>= \ ~(b, w') -> return (b, plusVarEnv_C (\ ~(id, x) ~(_, y) -> (id, unionVarSet x y)) w w')
instance MonadUnique LvlM where
  getUniqueSupplyM = LvlM $ getUniqueSupplyM >>= \a -> return (a, emptyVarEnv)

initLvl :: UniqSupply -> LvlM a -> a
initLvl us (LvlM m) = fst $ initUs_ us m

newPolyBndrs :: Level -> LevelEnv -> [OutVar] -> Bool -> [InId] -> LvlM (LevelEnv, [OutId])
-- The envt is extended to bind the new bndrs to dest_lvl, but
-- the le_ctxt_lvl is unaffected
newPolyBndrs dest_lvl
             env@(LE { le_lvl_env = lvl_env, le_subst = subst, le_env = id_env })
             abs_vars zapping_joins sorted_bndrs
 = ASSERT( all (not . isCoVar) bndrs )   -- What would we add to the CoSubst in this case. No easy answer.
   do { uniqs <- getUniquesM
      ; let new_bndrs = zipWith mk_poly_bndr bndrs uniqs
            bndr_prs  = bndrs `zip` new_bndrs
            env' = env { le_lvl_env = addLvls dest_lvl lvl_env new_bndrs
                       , le_subst   = foldl add_subst subst   bndr_prs
                       , le_env     = foldl add_id    id_env  bndr_prs }
      ; return (env', new_bndrs) }
  where
    bndrs = map unTag sorted_bndrs
    
    add_subst env (v, v') = extendIdSubst env v (mkVarApps (Var v') abs_vars)
    add_id    env (v, v') = extendVarEnv env v (v',abs_vars)

    mk_poly_bndr bndr uniq = transferPolyIdInfo bndr abs_vars $         -- Note [transferPolyIdInfo] in Id.hs
                             maybe_transfer_join_info bndr $
                             mkSysLocalOrCoVar (mkFastString str) uniq poly_ty
                           where
                             str     = (if isFinalPass env then "llf_" else "poly_")
                                                          ++ occNameString (getOccName bndr)
                             poly_ty = mkLamTypes abs_vars (substTy subst (idType bndr))
                             maybe_transfer_join_info bndr new_bndr
                               | not zapping_joins
                               , Just join_arity <- isJoinId_maybe bndr
                               = new_bndr `asJoinId` join_arity + length abs_vars
                               | otherwise
                               = new_bndr

newLvlVar :: LevelledExpr        -- The RHS of the new binding
          -> Bool                -- Whether it is bottom
          -> Maybe JoinArity     -- Its join arity, if it is a join point
          -> LvlM Id
newLvlVar lvld_rhs is_bot join_arity_maybe
  = do { uniq <- getUniqueM
       ; return (add_bot_info (add_join_info (mk_id uniq)))
       }
  where
    add_bot_info var  -- We could call annotateBotStr always, but the is_bot
                      -- flag just tells us when we don't need to do so
       | is_bot    = annotateBotStr var (exprBotStrictness_maybe de_tagged_rhs)
       | otherwise = var
    add_join_info var = var `asJoinId_maybe` join_arity_maybe
    de_tagged_rhs = deTagExpr lvld_rhs
    rhs_ty = exprType de_tagged_rhs
    mk_id uniq
      -- See Note [Grand plan for static forms] in SimplCore.
      | isJust (collectStaticPtrSatArgs lvld_rhs)
      = mkExportedVanillaId (mkSystemVarName uniq (mkFastString "static_ptr"))
                            rhs_ty
      | otherwise
      = mkLocalIdOrCoVar (mkSystemVarName uniq (mkFastString "lvl")) rhs_ty

cloneCaseBndrs :: LevelEnv -> Level -> [InVar] -> LvlM (LevelEnv, [Var])
cloneCaseBndrs env@(LE { le_subst = subst, le_lvl_env = lvl_env, le_env = id_env })
               new_lvl vs
  = do { us <- getUniqueSupplyM
       ; let (subst', vs') = cloneBndrs subst us (map unTag vs)
             env' = env { le_ctxt_lvl = new_lvl
                        , le_lvl_env  = addLvls new_lvl lvl_env vs'
                        , le_subst    = subst'
                        , le_env      = foldl add_id id_env (vs `zip` vs') }

       ; return (env', vs') }

cloneLetVars :: RecFlag -> LevelEnv -> Level -> Bool -> [InVar] -> LvlM (LevelEnv, [OutVar])
-- See Note [Need for cloning during float-out]
-- Works for Ids bound by let(rec)
-- The dest_lvl is attributed to the binders in the new env,
-- but cloneVars doesn't affect the le_ctxt_lvl of the incoming env
cloneLetVars is_rec
          env@(LE { le_subst = subst, le_lvl_env = lvl_env, le_env = id_env })
          dest_lvl zapping_joins vs
  = do { us <- getUniqueSupplyM
       ; let vs1  = map (zap_demand_info . maybe_zap_join . unTag) vs
                      -- See Note [Zapping the demand info]
             (subst', vs2) = case is_rec of
                               NonRecursive -> cloneBndrs      subst us vs1
                               Recursive    -> cloneRecIdBndrs subst us vs1
             prs  = vs `zip` vs2
             env' = env { le_lvl_env = addLvls dest_lvl lvl_env vs2
                        , le_subst   = subst'
                        , le_env     = foldl add_id id_env prs }

       ; return (env', vs2) }
  where
    maybe_zap_join v | isId v, zapping_joins = zapJoinId v
                     | otherwise             = v

add_id :: VarEnv (OutVar, [OutVar]) -> (InVar, Var) -> VarEnv (OutVar, [OutVar])
add_id id_env (TB v _, v1)
  | isTyVar v = delVarEnv    id_env v
  | isCoVar v = delVarEnv    id_env v
  | otherwise = extendVarEnv id_env v (v1,[])

zap_demand_info :: Var -> Var
zap_demand_info v
  | isId v    = zapIdDemandInfo v
  | otherwise = v

{-
Note [Preserving Fast Entries] (wrt Note [Late Lambda Floating])
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The policy: avoid changing fast entry invocations of free variables
(known call) into slow entry invocations of the new parameter
representing that free variable (unknown call).

  ... let f x = ... in
      let g x = ... (f ...) ... in  -- GOOD: call to f is fast entry
      ... g a ...

  => -- NB f wasn't floated

  poly_g f x = ... (f ...) ... -- BAD: call to f is slow entry

  ... let f x = ... in
      ... poly_g f a ...

The mechanism: when considering a let-bound lambda, we disallow the
float if any of the variables being abstracted over are applied in the
RHS. The flags -f(no)-late-abstract-undersat-var and
-f(no)-late-abstract-sat-var determine the details of this check.

It is intended that only applications of locally-bound free variables
*whose bindings are not themselves floated* can prevent a float. This
comes for free. The free variable information is not updated during
the setLevels pass. On the other hand, the set of abstracted variables
is calculated using the current LevelEnv. Thus: while a floated
function's original Id may be in the FII, it won't be in the
abs_vars.

Note [Zapping the demand info]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
VERY IMPORTANT: we must zap the demand info if the thing is going to
float out, because it may be less demanded than at its original
binding site.  Eg
   f :: Int -> Int
   f x = let v = 3*4 in v+x
Here v is strict; but if we float v to top level, it isn't any more.

Similarly, if we're floating a join point, it won't be one anymore, so we zap
join point information as well.

Note [The Reason SetLevels Does Substitution]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If a binding is going to be floated, setLevels carries a substitution
in order to eagerly replace that binding's occurrences with a
reference to the floated binding. Why doesn't it instead create a
simple binding right next to it and rely on the wise and weary
simplifier to handle the inlining? It's an issue with nested bindings.

  outer a = let x = ... a ... in
            let y = ... x ... in
            ... x ... y ...

Currently, when setLevels processes the x binding, the substitution
leads to the following intermediate step. (I am showing the result of
the substitution as if it were already applied.)

  x' a = ...

  out a = let y = ... x' a ... in
          ... x' a ... y ...

If we were to instead rely on the simplifier, we'd do something like this

  x' a = ...

  out a = let x = x' a in
          let y = ... x ... in
          ... x ... y ...

The problem here is that the subsequent step in which setLevels
analyzes the y binding would still treat x as y's only free
variable. With the eager substitution, on the other hand, x' is not
treated as a free variable since it's a global and a *is* recognized
as a free variable. That's the behavior we currently intend.

%************************************************************************
%*                                                                      *
\subsection{Determining unapplied variables}
%*                                                                      *
%************************************************************************
-}

-- Floating a closure does not affect the float decisions derived from
-- its body. Consequently, the lift decision for a function closure
-- should be based on the floats and silt of its original body.
--
-- But I want to isolate FVUp to analyzeFVs, so I add BSilt to each
-- interesting binder, to make the accurate body term available to
-- decideLateLambdaFloat.
data BSilt
  = BoringB
  | CloB FISilt

type CoreBindWithBoth = AnnBind InVar (DVarSet,FISilt)
type CoreExprWithBoth = AnnExpr InVar (DVarSet,FISilt)
type CoreAltWithBoth  = AnnAlt  InVar (DVarSet,FISilt)

siltOf :: CoreExprWithBoth -> FISilt
siltOf = snd . fst

fvsOf :: CoreExprWithBoth -> DVarSet
fvsOf = fst . fst

data FII = FII {fii_var :: !Var, fii_useInfo :: !UseInfo}

instance Outputable FII where
  ppr (FII v (unapplied,under,exact,over)) =
    ppr v <+> w '0' unapplied <> w '<' under <> w '=' exact <> w '>' over
    where w c b = if b then char c else empty

type UseInfo = (Bool,Bool,Bool,Bool)
  -- (unapplied,under sat,exactly sat,over sat)

bothUseInfo :: UseInfo -> UseInfo -> UseInfo
bothUseInfo (a,b,c,d) (w,x,y,z) = (a||w,b||x,c||y,d||z)

bothFII :: FII -> FII -> FII
bothFII (FII v l) (FII _ r) = FII v $ l `bothUseInfo` r

type FIIs = DVarEnv FII

emptyFIIs :: FIIs
emptyFIIs = emptyDVarEnv

unitFIIs :: Id -> UseInfo -> FIIs
unitFIIs v usage = extendDVarEnv emptyDVarEnv v $ FII v usage

bothFIIs :: FIIs -> FIIs -> FIIs
bothFIIs = plusDVarEnv_C bothFII

delBindersFVs :: [CoreBndr] -> DVarSet -> DVarSet
delBindersFVs bs fvs = foldr delBinderFVs fvs bs

delBinderFVs :: CoreBndr -> DVarSet -> DVarSet
-- see comment on CoreFVs.delBinderFV
delBinderFVs bndr fvs
  = fvs `delDVarSet` bndr
        `unionDVarSet` (fvDVarSet $ varTypeTyCoFVs bndr)

{-

%************************************************************************
%*                                                                      *
\subsection{Free variables (and types) and unapplied variables}
%*                                                                      *
%************************************************************************
-}

-- Note [Approximating CorePrep]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- In order to more accurately predict the cost of lifting a function
-- binding, we approximate CorePrep's floats. For example, CorePrep
-- changes
--
--   let t = let x = f s
--           in (x, s)
--
-- to
--
--   let x = f s
--       t = (x, s)
--
-- Before CorePrep, f occurs free both in t and in x. After CorePrep,
-- f occurs only in t. Therefore, we must approximate CorePrep's
-- floating in order to see that f does not occur in t, else the
-- incorrectly predicted growth of t will be included in the estimated
-- cost of lifting f.
--
-- NB That floating cannot change the abs_ids of a function closure
-- because nothing floats past a lambda. TODO What about zero-arity
-- LNEs?
--
-- We are *approximating* CorePrep because we do not actually float
-- anything: thus some of the emulated decisions might be
-- inaccurate. There are three functions that CorePrep uses to make
-- decisions about floats:
--
--   * cpe_ExprIsTrivial - that was pretty easy to replicate; I think
--   it's accurately emulated via the fvu_isTrivial field.
--
--   * exprIsHNF - non-trivial definition; foolish to
--   replicate. HOWEVER: calling this on the original term instead of
--   the CorePrep'd term still accurately emulates CorePrep: the
--   definition of exprIsHNF is insensitive to the things that
--   CorePrep changes (lets and the structure of arguments).
--
--   * exprOkForSpeculation - non-trivial definition; foolish to
--   replicate. Thus I call this on the original term instead of the
--   CorePrep'd term. Doing so may make the emulation of CorePrep
--   floats potentially inaccurate.
--
-- TODO improve the exprOkForSpeculation approximation?

data FIFloats = FIFloats
  !OkToSpec
  ![ArgRep] -- the type of each sat bindings that is floating
  !DVarSet -- the ids of the non-sat bindings that are floating
  !FIIs -- use information for ids free in the floating bindings
  !Skeleton -- the skeleton of all floating bindings

data FISilt = FISilt
  ![ArgRep] -- the type of each free sat id
  !FIIs -- use information for free ids
  !Skeleton -- the skeleton

instance Outputable FISilt where
  ppr (FISilt satReps fiis sk) = ppr (length satReps) <+> ppr (dVarEnvElts fiis) $$ ppr sk

siltFIIs :: FISilt -> FIIs
siltFIIs (FISilt _ fiis _) = fiis

emptyFloats :: FIFloats
emptyFloats = FIFloats OkToSpec [] emptyDVarSet emptyFIIs NilSk

emptySilt :: FISilt
emptySilt = FISilt [] emptyDVarEnv NilSk

delBindersSilt :: [CoreBndr] -> FISilt -> FISilt
delBindersSilt bs (FISilt m fiis sk) =
  FISilt m (fiis `delDVarEnvList` bs) sk

isEmptyFloats :: FIFloats -> Bool
isEmptyFloats (FIFloats _ n bndrs _ _) = null n && isEmptyDVarSet bndrs

appendFloats :: FIFloats -> FIFloats -> FIFloats
appendFloats (FIFloats ok1 n1 bndrs1 fiis1 sk1) (FIFloats ok2 n2 bndrs2 fiis2 sk2) =
  FIFloats (combineOkToSpec ok1 ok2)
    (n1 ++ n2)
    (bndrs1 `unionDVarSet` bndrs2)
    (bothFIIs fiis1 $ fiis2 `minusDVarEnv` bndrs1)
    (sk1 `bothSk` sk2)

bothSilt :: FISilt -> FISilt -> FISilt
bothSilt (FISilt m1 fiis1 sk1) (FISilt m2 fiis2 sk2) =
  FISilt (m1 ++ m2)
    (fiis1 `bothFIIs` fiis2)
    (sk1 `bothSk` sk2)

altSilt :: FISilt -> FISilt -> FISilt
altSilt (FISilt m1 fiis1 sk1) (FISilt m2 fiis2 sk2) =
  FISilt (m1 ++ m2)
    (fiis1 `bothFIIs` fiis2)
    (sk1 `altSk` sk2)

-- corresponds to CorePrep.wrapBinds
wrapFloats :: FIFloats -> FISilt -> FISilt
wrapFloats (FIFloats _ n bndrs fiis1 skFl) (FISilt m fiis2 skBody) =
  FISilt (m Data.List.\\ n) -- floated sat ids are always OccOnce!, so
                            -- it's correct to remove them 1-for-1
    (bothFIIs fiis1 $ minusDVarEnv fiis2 bndrs)
    (skFl `bothSk` skBody)

-- corresponds to CorePrep.wantFloatNested
--
-- NB bindings only float out of a closure when that would reveal a
-- head normal form
wantFloatNested :: RecFlag -> Bool -> FIFloats -> CoreExpr -> Bool
wantFloatNested is_rec strict_or_unlifted floats rhs
  =  isEmptyFloats floats
  || strict_or_unlifted
  || (allLazyNested is_rec floats && exprIsHNF rhs)

perhapsWrapFloatsFVUp :: RecFlag -> Bool -> CoreExpr -> FVUp -> FVUp
perhapsWrapFloatsFVUp is_rec use_case e e_up =
  -- do bindings float out of the argument?
  if wantFloatNested is_rec use_case (fvu_floats e_up) e
  then e_up -- yes, they do
  else lambdaLikeFVUp [] e_up


-- must correspond to CorePrep.allLazyNested
allLazyNested :: RecFlag -> FIFloats -> Bool
allLazyNested is_rec (FIFloats okToSpec _ _ _ _) = case okToSpec of
  OkToSpec    -> True
  NotOkToSpec -> False
  IfUnboxedOk -> isNonRec is_rec

newtype Identity a = Identity {runIdentity :: a}
instance Functor Identity where fmap = Control.Monad.liftM
instance Applicative Identity where
  pure = Identity
  (<*>) = Control.Monad.ap
instance Monad Identity where
  return = pure
  Identity a >>= f = f a
type FVM = Identity

-- Note [FVUp]
-- ~~~~~~~~~~~
-- An FVUp simultaneously maintains two views on an expression:
--
--   1) the actual expression E, as well as
--
--   2) the pair of floats F and expression E' that would result from CorePrep's floating.
--
-- NB We don't actually do any floating, but we anticipate it.

-- Note [recognizing LNE]
-- ~~~~~~~~~~~~~~~~~~~~~~
--
-- (This is now performed in the CoreJoins module.)
--
-- We track escaping variables in order to recognize LNEs. This helps
-- in a couple of ways:
--
--  (1) it is ok to lift a "thunk" if it is actually LNE
--
--  (2) LNEs are not actually closures, so adding free variables to
--      one does not increase allocation (cf closureFVUp)
--
-- (See Note [FVUp] for the semantics of E, F, and E'.)
--
-- NB The escaping variables in E are the same as the escaping
-- variables in F and E'. A deceptive example suggesting they might
-- instead be different is this sort of floating:
--
--   let t = lne j = ...
--           in E[j]
--
-- becomes
--
--   let j = ...
--       t = E[j]
--
-- Since j hypothetically floated out of t, it is no longer
-- LNE. However, this example is impossible: j would not float out of
-- t. A binding only floats out of a closure if doing so would reveal
-- a head normal form (cf wantFloatNested and CoreUtil's Note
-- [exprIsHNF]), and for all such forms, the free ids of the arguments
-- are defined to be escaping. Thus: LNE bindings do not float out of
-- closures.

-- Note [FVUp for closures and floats]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- See Note [FVUp] for the semantics of F and E'.
--
-- When a pair F and E' is itself floated, it becomes one of
--
--   (F; let n = E'        , n)
--
-- or
--
--   (F; case E' of n ->   , n)
--
-- closureFVUp manages the let-binding of E'
--
-- floatFVUp manages the whole transformation

-- see Note [FVUp] for semantics of E, F, and E'
data FVUp = FVUp {
  fvu_fvs :: DVarSet,  -- free vars of E
  
  fvu_floats :: FIFloats, -- the floats, F

  fvu_silt :: FISilt, -- the things that did not float, E'

  fvu_isTrivial :: Bool
    -- fvu_isTrivial up <=> cpe_ExprIsTrivial (perhapsWrapFloatsFVUp up)
  }

litFVUp :: FVUp
litFVUp = FVUp {
  fvu_fvs = emptyDVarSet,
  fvu_floats = emptyFloats,
  fvu_silt = emptySilt,
  fvu_isTrivial = True
  }

typeFVUp :: DVarSet -> FVUp
typeFVUp tyvars = litFVUp {fvu_fvs = tyvars}

varFVUp :: Var -> Bool -> UseInfo -> FVUp
varFVUp v nonTopLevel usage = FVUp {
  fvu_fvs     = if local                  then unitDVarSet v      else emptyDVarSet,
  fvu_floats  = emptyFloats,
  fvu_silt = if nonTopLevel then FISilt [] (unitFIIs v usage) NilSk else emptySilt,
  fvu_isTrivial = True
  }
  where local = isLocalVar v

lambdaLikeFVUp :: [CoreBndr] -> FVUp -> FVUp
-- nothing floats past a lambda
--
-- also called for case alternatives
lambdaLikeFVUp bs up = up {
  fvu_fvs = del (fvu_fvs up),
  fvu_floats = emptyFloats,
  fvu_silt = delBindersSilt bs $ fvu_floats up `wrapFloats` fvu_silt up
  }
  where del = delBindersFVs bs

-- see Note [FVUp for closures and floats]
floatFVUp :: FVEnv -> Maybe CoreBndr -> Bool -> CoreExprWithCxts -> FVUp -> FVUp
floatFVUp env mb_id use_case rhs up =
  let rhs_floats@(FIFloats _ _ bndrs_floating_out _ _) = fvu_floats up

      join_arity = case mb_id of Nothing       -> Nothing -- floating an argument
                                 Just b        -> isJoinId_maybe b

      FISilt m fids sk = fvu_silt up

      new_float = FIFloats okToSpec n bndrs fids sk'
        where
          okToSpec | use_case  = if exprOkForSpeculation rhs
                                 then IfUnboxedOk else NotOkToSpec
                   | otherwise = OkToSpec

          (n,bndrs) = case mb_id of
            Nothing -> ((toArgRep $ typePrimRep $ exprType rhs):m,emptyDVarSet)
            Just id -> (m,unitDVarSet id)

          -- treat LNEs like cases; see Note [recognizing LNE]
          sk' | use_case || (fve_ignoreLNEClo env && isJust join_arity) = sk
              | otherwise = CloSk mb_id fids' sk

                where fids' = bndrs_floating_out `unionDVarSet` mapDVarEnv fii_var fids
                  -- add in the binders floating out of this binding
                  --
                  -- TODO is this redundant?
  in up {
    -- we are *moving* the fvu_silt to a new float
    fvu_floats = rhs_floats `appendFloats` new_float,
    fvu_silt = emptySilt
    }

data FVEnv = FVEnv
  { fve_isFinal      :: !Bool
  , fve_useDmd       :: !Bool
  , fve_ignoreLNEClo :: !Bool
  , fve_floatLNE0    :: !Bool
  , fve_argumentDemands :: Maybe [Bool]
  , fve_runtimeArgs  :: !NumRuntimeArgs
  , fve_letBoundVars :: !(IdEnv Bool)
  , fve_nonTopLevel  :: !IdSet
  -- ^ the non-TopLevel variables in scope
  }

type NumRuntimeArgs = Int -- i <=> applied to i runtime arguments

initFVEnv :: Maybe FinalPassSwitches -> FVEnv
initFVEnv mb_fps = FVEnv {
  fve_isFinal = isFinal,
  fve_useDmd = useDmd,
  fve_ignoreLNEClo = ignoreLNEClo,
  fve_floatLNE0 = floatLNE0,
  fve_argumentDemands = Nothing,
  fve_runtimeArgs = 0,
  fve_letBoundVars = emptyVarEnv,
  fve_nonTopLevel = emptyVarSet
  }
  where (isFinal, useDmd, ignoreLNEClo, floatLNE0) = case mb_fps of
          Nothing -> (False, False, False, False)
          Just fps -> (True, fps_strictness fps, fps_ignoreLNEClo fps, fps_floatLNE0 fps)

unappliedEnv :: FVEnv -> FVEnv
unappliedEnv env = env { fve_runtimeArgs = 0, fve_argumentDemands = Nothing }

appliedEnv :: FVEnv -> FVEnv
appliedEnv env =
  env { fve_runtimeArgs = 1 + fve_runtimeArgs env }

letBoundEnv :: CoreBndr -> CoreExprWithCxts -> FVEnv -> FVEnv
letBoundEnv bndr rhs env =
   env { fve_letBoundVars = extendVarEnv_C (\_ new -> new)
           (fve_letBoundVars env)
           bndr
           (isFunction rhs) }

letBoundsEnv :: [(CoreBndr, CoreExprWithCxts)] -> FVEnv -> FVEnv
letBoundsEnv binds env = foldl (\e (id, rhs) -> letBoundEnv id rhs e) env binds

extendEnv :: [CoreBndr] -> FVEnv -> FVEnv
extendEnv bndrs env =
  env { fve_nonTopLevel = extendVarSetList (fve_nonTopLevel env) bndrs }

-- | Annotate a 'CoreExpr' with its non-TopLevel free type and value
-- variables and its unapplied variables at every tree node
analyzeFVs :: FVEnv -> CoreExprWithCxts -> CoreExprWithBoth
analyzeFVs env e = fst $ runIdentity $ analyzeFVsM env e

boringBinder :: CoreBndr -> InVar
boringBinder b = TB b BoringB

ret :: FVUp -> a -> FVM (((DVarSet,FISilt), a), FVUp)
ret up x = return (((fvu_fvs up,fvu_silt up),x),up)

analyzeFVsM :: FVEnv -> CoreExpr -> FVM (CoreExprWithBoth, FVUp)
analyzeFVsM env (splitCxt -> InNewCxt cid body)
  = do (body', up) <- analyzeFVsM env body
       ret up $ markAnnCxt ann (boringBinder cid) (idType cid) body'
  where
    ann = (emptyDVarSet, emptySilt)
      -- Don't bother annotating a context marker (just a fake let binding)

analyzeFVsM  env (Var v) = ret up $ AnnVar v where
  up = varFVUp v nonTopLevel usage

  n_runtime_args = fve_runtimeArgs env

  nonTopLevel = v `elemVarSet` fve_nonTopLevel env

  arity = idArity v
  usage = (0     == n_runtime_args -- unapplied
          ,w $ arity >  n_runtime_args -- too few args
          ,w $ arity == n_runtime_args -- exact args
          ,w $ arity <  n_runtime_args -- too many args
          )
    where w x = (0 /= n_runtime_args) && x

analyzeFVsM _env (Lit lit) = ret litFVUp $ AnnLit lit

analyzeFVsM  env (Lam b body) = do
  (body', body_up) <- flip analyzeFVsM body $ extendEnv [b] $ unappliedEnv env

  let oneshot = isId b && isOneShotBndr b

  let up = lambdaLikeFVUp [b] body_up

      up' = up {
        fvu_silt = case fvu_silt up of
          FISilt m fiis sk -> FISilt m fiis $ lamSk oneshot sk,

        fvu_isTrivial = isTyVar b && fvu_isTrivial body_up
        }

  ret up' $ AnnLam (boringBinder b) body'

analyzeFVsM  env app@(App fun arg) = do
  -- step 0: compute the function's effective strictness signature
  let argDmds = case fve_argumentDemands env of
        Nothing   -> computeArgumentDemands app
        Just dmds -> dmds

  let (argIsStrictlyDemanded, dmds')
        | isTyCoArg arg = (False, argDmds)
        | otherwise     = case argDmds of
        [] -> (False, []) -- we couldn't determine argument strictness
                          -- for this application
        isStrDmd : dmds -> (isStrDmd, dmds)

      funEnv = env { fve_argumentDemands = Just dmds' }

  -- step 1: recurse
  (arg2, arg_up) <- analyzeFVsM (unappliedEnv env) arg

  (fun2, fun_up) <- flip analyzeFVsM fun $ if isRuntimeArg arg
                                           then appliedEnv funEnv
                                           else            funEnv

  -- step 2: approximate floating the argument
  let is_strict   = fve_useDmd env && argIsStrictlyDemanded
      is_unlifted = isUnliftedType $ exprType arg
      use_case    = is_strict || is_unlifted

  let rhs = arg
      rhs_up = perhapsWrapFloatsFVUp NonRecursive use_case arg arg_up

  let binding_up = -- does the argument itself float?
        if fvu_isTrivial rhs_up
        then rhs_up -- no, it does not
        else floatFVUp env Nothing use_case rhs rhs_up

  -- lastly: merge the Ups
  let up = fun_up {
        fvu_fvs     = fvu_fvs    fun_up `unionDVarSet` fvu_fvs arg_up,

        fvu_floats  = fvu_floats fun_up `appendFloats` fvu_floats  binding_up,
        fvu_silt    = fvu_silt   fun_up `bothSilt`     fvu_silt    binding_up,

        fvu_isTrivial = isTypeArg arg && fvu_isTrivial fun_up
        }

  ret up $ AnnApp fun2 arg2

analyzeFVsM env (Case scrut bndr ty alts) = do
  let tyfvs = tyCoVarsOfTypeDSet ty

  let rEnv = unappliedEnv env

  (scrut2, scrut_up) <- analyzeFVsM rEnv scrut
  let scrut_fvs = fvu_fvs scrut_up

  (pairs, rhs_up_s) <-
    flip mapAndUnzipM alts $ \(con,args,rhs) -> do
      (rhs2, rhs_up) <- analyzeFVsM (extendEnv (bndr : args) rEnv) rhs
          -- nothing floats out of an alt
      ret (lambdaLikeFVUp args rhs_up) (con, map boringBinder args, rhs2)

  let alts2 = snd $ unzip pairs

  let alts_silt = foldr altSilt emptySilt    $ map fvu_silt rhs_up_s

  let up = FVUp {
        fvu_fvs = unionDVarSets (map fvu_fvs rhs_up_s)
                       `delDVarSet` bndr
                       `unionDVarSet` scrut_fvs
                       `unionDVarSet` tyfvs,

        fvu_floats = fvu_floats scrut_up, -- nothing floats out of an alt
        fvu_silt   = fvu_silt scrut_up `bothSilt` delBindersSilt [bndr] alts_silt,

        fvu_isTrivial = False
        }

  ret up $ AnnCase scrut2 (boringBinder bndr) ty alts2

analyzeFVsM env (Let (NonRec binder rhs) body) = do
  -- step 1: recurse
  let rEnv = unappliedEnv env
  (rhs2, rhs_up) <- analyzeFVsM rEnv rhs
  (body2, body_up) <- flip analyzeFVsM body $ extendEnv [binder] $ letBoundEnv binder rhs rEnv

  -- step 2: approximate floating the binding
  let is_strict   = fve_useDmd env && isStrictDmd (idDemandInfo binder)
      is_unlifted = isUnliftedType $ varType binder
      use_case    = is_strict || is_unlifted

  let binding_up = floatFVUp env (Just binder) use_case rhs $
                   perhapsWrapFloatsFVUp NonRecursive use_case rhs rhs_up

  let rule_and_unfolding_vars | isId binder = idRuleAndUnfoldingVarsDSet binder
                              | otherwise   = emptyDVarSet

  -- lastly: merge the Ups
  let up = FVUp {
        fvu_fvs = fvu_fvs binding_up
                    `unionDVarSet` (fvu_fvs body_up `delDVarSet` binder)
                    `unionDVarSet` rule_and_unfolding_vars,

        fvu_floats = fvu_floats binding_up `appendFloats` fvu_floats body_up,
        fvu_silt = delBindersSilt [binder] $ fvu_silt body_up,

        fvu_isTrivial = fvu_isTrivial body_up
        }

  -- extra lastly: tag the binder with LNE and its use info in both
  -- its whole scope
  let bsilt = CloB $ fvu_floats body_up `wrapFloats` fvu_silt body_up

  ret up $ AnnLet (AnnNonRec (TB binder bsilt) rhs2) body2

analyzeFVsM env (Let (Rec binds) body) = do
  let binders = map fst binds
  let is_joins = map (isJust . isJoinId_maybe) binders
      is_join  = head is_joins

  MASSERT(all (== is_join) is_joins)

  -- step 1: recurse
  let recurse = analyzeFVsM $ unappliedEnv $ extendEnv binders $ letBoundsEnv binds env
  (rhss2,rhs_up_s) <- flip mapAndUnzipM binds $ \(_,rhs) -> do
    (rhss2,rhs_up) <- recurse rhs
    return $ (,) rhss2 $ perhapsWrapFloatsFVUp Recursive False rhs rhs_up
  (body2,body_up) <- recurse body

  -- step 2: approximate floating the bindings
  let binding_up_s = flip map (zip binds rhs_up_s) $ \((binder,rhs),rhs_up) ->
        floatFVUp env (Just binder) False rhs $
        rhs_up {fvu_silt = delBindersSilt [binder] (fvu_silt rhs_up)}

  -- lastly: merge Ups
  let up = FVUp {
        fvu_fvs = delBindersFVs binders $
                  fvu_fvs body_up `unionDVarSet`
                    computeRecRHSsFVs binders (map fvu_fvs binding_up_s),

        fvu_floats = foldr appendFloats (fvu_floats body_up) $ map fvu_floats binding_up_s,
        fvu_silt   = delBindersSilt binders $ fvu_silt body_up,

        fvu_isTrivial = fvu_isTrivial body_up
        }

  -- extra lastly: tag the binders with use info in the
  -- whole scope (ie including all RHSs). the bsilt is the same for each binder.
  let bsilt = CloB scope_silt where
        body_silt  = fvu_floats body_up `wrapFloats` fvu_silt body_up
        scope_silt = foldr bothSilt body_silt $ map fvu_silt rhs_up_s
                       -- NB rhs_up_s have already been wrapFloat'd

  ret up $ AnnLet (AnnRec ([TB bndr bsilt | bndr <- binders] `zip` rhss2)) body2

analyzeFVsM  env (Cast expr co) = do
  let cfvs = tyCoVarsOfCoDSet co

  (expr2,up) <- analyzeFVsM env expr

  let up' = up { fvu_fvs = fvu_fvs up `unionDVarSet` cfvs
               , fvu_isTrivial = False
               }

  ret up' $ AnnCast expr2 ((cfvs,emptySilt),co)

analyzeFVsM  env (Tick tickish expr) = do
  let tfvs = case tickish of
        Breakpoint _ ids -> mkDVarSet ids
        _ -> emptyDVarSet

  (expr2,up) <- analyzeFVsM env expr

  let up' = up { fvu_fvs = fvu_fvs up `unionDVarSet` tfvs
               , fvu_isTrivial = not (tickishIsCode tickish) && fvu_isTrivial up
               }

  ret up' $ AnnTick tickish expr2

analyzeFVsM _env (Type ty) = ret (typeFVUp $ tyCoVarsOfTypeDSet ty) $ AnnType ty

analyzeFVsM _env (Coercion co) = ret (typeFVUp $ tyCoVarsOfCoDSet co) $ AnnCoercion co



computeRecRHSsFVs :: [CoreBndr] -> [DVarSet] -> DVarSet
computeRecRHSsFVs binders rhs_fvs =
  foldr (unionDVarSet . idRuleAndUnfoldingVarsDSet)
        (foldr unionDVarSet emptyDVarSet rhs_fvs)
        binders

-- should mirror CorePrep.cpeApp.collect_args
computeArgumentDemands :: CoreExpr -> [Bool]
computeArgumentDemands e = go e 0 where
  go (App f a) as | isRuntimeArg a = go f (1 + as)
                  | otherwise      = go f as
  go (Cast f _) as = go f as
  go (Tick _ f) as = go f as
  go e          as = case e of
    Var fid | length argStricts <= as -> -- at least saturated
      reverse argStricts ++ replicate (as - length argStricts) False
      where argStricts = map isStrictDmd $ fst $ splitStrictSig $ idStrictness fid
    _       -> []





data Skeleton -- an abstraction of a term retaining only information
              -- relevant to estimating lambda lifting's effect on the
              -- heap footprints of closures
  = NilSk
  | CloSk (Maybe Id) DVarSet Skeleton
     -- a closure's free (non-sat) ids and its rhs
  | BothSk Skeleton Skeleton
  | LamSk Bool Skeleton -- we treat oneshot lambdas specially
  | AltSk Skeleton Skeleton -- case alternatives
instance Outputable Skeleton where
  ppr NilSk = text ""
  ppr (CloSk mb_id ids sk) = hang (nm <+> ppr (dVarSetElems ids)) 2 (parens $ ppr sk)
    where nm = case mb_id of
            Nothing -> text "ARG"
            Just id -> text "CLO" <+> ppr id
  ppr (BothSk sk1 sk2) = ppr sk1 $$ ppr sk2
  ppr (LamSk oneshot sk) = char '\\' <> (if oneshot then char '1' else empty) <+> ppr sk
  ppr (AltSk sk1 sk2) = vcat [ text "{ " <+> ppr sk1
                             , text "ALT"
                             , text "  " <+> ppr sk2
                             , text "}" ]

bothSk :: Skeleton -> Skeleton -> Skeleton
bothSk NilSk r = r
bothSk l NilSk = l
bothSk l r = BothSk l r

lamSk :: Bool -> Skeleton -> Skeleton
lamSk oneshot sk = case sk of
  NilSk -> sk
  LamSk oneshot' sk' | oneshot && oneshot' -> sk
                     | otherwise -> LamSk False sk'
  _ -> LamSk oneshot sk

altSk :: Skeleton -> Skeleton -> Skeleton
altSk NilSk r = r
altSk l NilSk = l
altSk l r = AltSk l r

-- type OldId = Id
type NewId = Id
type OldIdSet = DIdSet
type NewIdSet = DIdSet
costToLift :: (OldIdSet -> NewIdSet) -> (Id -> WordOff) ->
  NewId -> NewIdSet -> -- the function binder and its free ids
  Skeleton -> -- abstraction of the scope of the function
  (WordOff, WordOff) -- ( closure growth , closure growth in lambda )
costToLift expander sizer f abs_ids = go where
  go sk = case sk of
    NilSk -> (0,0)
    CloSk _ (expander -> fids) rhs -> -- NB In versus Out ids
      let (!cg1,!cgil1) = go rhs
          cg | f `elemDVarSet` fids =
               let newbies = abs_ids `minusDVarSet` fids
               in foldDVarSet (\id size -> sizer id + size) (0 - sizer f) newbies
             | otherwise           = 0
            -- (max 0) the growths from the RHS, since the closure
            -- might not be entered
            --
            -- in contrast, the effect on the closure's allocation
            -- itself is certain
      in (cg + max 0 cg1, max 0 cgil1)
    BothSk sk1 sk2 -> let (!cg1,!cgil1) = go sk1
                          (!cg2,!cgil2) = go sk2
                       -- they are under different lambdas (if any),
                       -- so we max instead of sum, since their
                       -- multiplicities could differ
                      in (cg1 + cg2   ,   cgil1 `max` cgil2)
    LamSk oneshot sk -> case go sk of
      (cg, cgil) -> if oneshot
                    then (   max 0 $ cg + cgil   ,   0) -- zero entries or one
                    else (0   ,   cg `max` cgil   ) -- perhaps several entries
    AltSk sk1 sk2 -> let (!cg1,!cgil1) = go sk1
                         (!cg2,!cgil2) = go sk2
                     in (   cg1 `max` cg2   ,   cgil1 `max` cgil2   )
