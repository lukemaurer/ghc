{-# LANGUAGE CPP #-}

-- | Handy functions for creating much Core syntax
module MkCore (
        -- * Constructing normal syntax
        mkCoreLet, mkCoreLets,
        mkCoreApp, mkCoreApps, mkCoreConApps,
        mkCoreLams, mkWildCase, mkIfThenElse,
        mkWildValBinder, mkWildEvBinder,
        sortQuantVars, castBottomExpr,
        mkParallelBindings,

        -- * Constructing boxed literals
        mkWordExpr, mkWordExprWord,
        mkIntExpr, mkIntExprInt,
        mkIntegerExpr,
        mkFloatExpr, mkDoubleExpr,
        mkCharExpr, mkStringExpr, mkStringExprFS,

        -- * Floats
        FloatBind(..), wrapFloat,

        -- * Constructing small tuples
        mkCoreVarTup, mkCoreVarTupTy, mkCoreTup, mkCoreUbxTup,
        mkCoreTupBoxity,

        -- * Constructing big tuples
        mkBigCoreVarTup, mkBigCoreVarTup1,
        mkBigCoreVarTupTy, mkBigCoreTupTy,
        mkBigCoreTup,

        -- * Deconstructing small tuples
        mkSmallTupleSelector, mkSmallTupleCase,

        -- * Deconstructing big tuples
        mkTupleSelector, mkTupleSelector1, mkTupleCase,

        -- * Constructing list expressions
        mkNilExpr, mkConsExpr, mkListExpr,
        mkFoldrExpr, mkBuildExpr,

        -- * Constructing Maybe expressions
        mkNothingExpr, mkJustExpr,

        -- * Error Ids
        mkRuntimeErrorApp, mkImpossibleExpr, errorIds,
        rEC_CON_ERROR_ID, iRREFUT_PAT_ERROR_ID, rUNTIME_ERROR_ID,
        nON_EXHAUSTIVE_GUARDS_ERROR_ID, nO_METHOD_BINDING_ERROR_ID,
        pAT_ERROR_ID, rEC_SEL_ERROR_ID, aBSENT_ERROR_ID,
        tYPE_ERROR_ID
    ) where

#include "HsVersions.h"

import Id
import Var      ( EvVar, setTyVarUnique )

import CoreSyn
import CoreUtils        ( exprType, needsCaseBinding, bindNonRec )
import Literal
import HscTypes

import TysWiredIn
import PrelNames

import HsUtils          ( mkChunkified, chunkify )
import TcType           ( mkSpecSigmaTy )
import Type
import Coercion         ( isCoVar )
import TysPrim
import DataCon          ( DataCon, dataConWorkId )
import IdInfo           ( vanillaIdInfo, setStrictnessInfo,
                          setArityInfo )
import Demand
import Name      hiding ( varName )
import Outputable
import FastString
import UniqSupply
import BasicTypes
import Util
import DynFlags
import VarEnv
import Data.List

import Data.Char        ( ord )

infixl 4 `mkCoreApp`, `mkCoreApps`

{-
************************************************************************
*                                                                      *
\subsection{Basic CoreSyn construction}
*                                                                      *
************************************************************************
-}
sortQuantVars :: [Var] -> [Var]
-- Sort the variables, putting type and covars first, in scoped order,
-- and then other Ids
-- It is a deterministic sort, meaining it doesn't look at the values of
-- Uniques. For explanation why it's important See Note [Unique Determinism]
-- in Unique.
sortQuantVars vs = sorted_tcvs ++ ids
  where
    (tcvs, ids) = partition (isTyVar <||> isCoVar) vs
    sorted_tcvs = toposortTyVars tcvs

-- | Bind a binding group over an expression, using a @let@ or @case@ as
-- appropriate (see "CoreSyn#let_app_invariant")
mkCoreLet :: CoreBind -> CoreExpr -> CoreExpr
mkCoreLet (NonRec bndr rhs) body        -- See Note [CoreSyn let/app invariant]
  | needsCaseBinding (idType bndr) rhs
  , not (isJoinId bndr)
  = Case rhs bndr (exprType body) [(DEFAULT,[],body)]
mkCoreLet bind body
  = Let bind body

-- | Bind a list of binding groups over an expression. The leftmost binding
-- group becomes the outermost group in the resulting expression
mkCoreLets :: [CoreBind] -> CoreExpr -> CoreExpr
mkCoreLets binds body = foldr mkCoreLet body binds

-- | Construct an expression which represents the application of one expression
-- to the other
mkCoreApp :: SDoc -> CoreExpr -> CoreExpr -> CoreExpr
-- Respects the let/app invariant by building a case expression where necessary
--   See CoreSyn Note [CoreSyn let/app invariant]
mkCoreApp _ fun (Type ty)     = App fun (Type ty)
mkCoreApp _ fun (Coercion co) = App fun (Coercion co)
mkCoreApp d fun arg           = ASSERT2( isFunTy fun_ty, ppr fun $$ ppr arg $$ d )
                                mk_val_app fun arg arg_ty res_ty
                              where
                                fun_ty = exprType fun
                                (arg_ty, res_ty) = splitFunTy fun_ty

-- | Construct an expression which represents the application of a number of
-- expressions to another. The leftmost expression in the list is applied first
-- Respects the let/app invariant by building a case expression where necessary
--   See CoreSyn Note [CoreSyn let/app invariant]
mkCoreApps :: CoreExpr -> [CoreExpr] -> CoreExpr
-- Slightly more efficient version of (foldl mkCoreApp)
mkCoreApps orig_fun orig_args
  = go orig_fun (exprType orig_fun) orig_args
  where
    go fun _      []               = fun
    go fun fun_ty (Type ty : args) = go (App fun (Type ty)) (piResultTy fun_ty ty) args
    go fun fun_ty (arg     : args) = ASSERT2( isFunTy fun_ty, ppr fun_ty $$ ppr orig_fun
                                                              $$ ppr orig_args )
                                     go (mk_val_app fun arg arg_ty res_ty) res_ty args
                                   where
                                     (arg_ty, res_ty) = splitFunTy fun_ty

-- | Construct an expression which represents the application of a number of
-- expressions to that of a data constructor expression. The leftmost expression
-- in the list is applied first
mkCoreConApps :: DataCon -> [CoreExpr] -> CoreExpr
mkCoreConApps con args = mkCoreApps (Var (dataConWorkId con)) args

mk_val_app :: CoreExpr -> CoreExpr -> Type -> Type -> CoreExpr
-- Build an application (e1 e2),
-- or a strict binding  (case e2 of x -> e1 x)
-- using the latter when necessary to respect the let/app invariant
--   See Note [CoreSyn let/app invariant]
mk_val_app fun arg arg_ty res_ty
  | not (needsCaseBinding arg_ty arg)
  = App fun arg                -- The vastly common case

  | otherwise
  = Case arg arg_id res_ty [(DEFAULT,[],App fun (Var arg_id))]
  where
    arg_id = mkWildValBinder arg_ty
        -- Lots of shadowing, but it doesn't matter,
        -- because 'fun ' should not have a free wild-id
        --
        -- This is Dangerous.  But this is the only place we play this
        -- game, mk_val_app returns an expression that does not have
        -- have a free wild-id.  So the only thing that can go wrong
        -- is if you take apart this case expression, and pass a
        -- fragmet of it as the fun part of a 'mk_val_app'.

-----------
mkWildEvBinder :: PredType -> EvVar
mkWildEvBinder pred = mkWildValBinder pred

-- | Make a /wildcard binder/. This is typically used when you need a binder
-- that you expect to use only at a *binding* site.  Do not use it at
-- occurrence sites because it has a single, fixed unique, and it's very
-- easy to get into difficulties with shadowing.  That's why it is used so little.
-- See Note [WildCard binders] in SimplEnv
mkWildValBinder :: Type -> Id
mkWildValBinder ty = mkLocalIdOrCoVar wildCardName ty

mkWildCase :: CoreExpr -> Type -> Type -> [CoreAlt] -> CoreExpr
-- Make a case expression whose case binder is unused
-- The alts should not have any occurrences of WildId
mkWildCase scrut scrut_ty res_ty alts
  = Case scrut (mkWildValBinder scrut_ty) res_ty alts

mkIfThenElse :: CoreExpr -> CoreExpr -> CoreExpr -> CoreExpr
mkIfThenElse guard then_expr else_expr
-- Not going to be refining, so okay to take the type of the "then" clause
  = mkWildCase guard boolTy (exprType then_expr)
         [ (DataAlt falseDataCon, [], else_expr),       -- Increasing order of tag!
           (DataAlt trueDataCon,  [], then_expr) ]

castBottomExpr :: CoreExpr -> Type -> CoreExpr
-- (castBottomExpr e ty), assuming that 'e' diverges,
-- return an expression of type 'ty'
-- See Note [Empty case alternatives] in CoreSyn
castBottomExpr e res_ty
  | e_ty `eqType` res_ty = e
  | otherwise            = Case e (mkWildValBinder e_ty) res_ty []
  where
    e_ty = exprType e

{-
The functions from this point don't really do anything cleverer than
their counterparts in CoreSyn, but they are here for consistency
-}

-- | Create a lambda where the given expression has a number of variables
-- bound over it. The leftmost binder is that bound by the outermost
-- lambda in the result
mkCoreLams :: [CoreBndr] -> CoreExpr -> CoreExpr
mkCoreLams = mkLams

-- | Create several independent non-recursive let bindings, such that no binding
-- captures a variable free in another binding. This is accomplished by renaming
-- any stale binder and then putting an extra let after the bindings. Thus, the
-- the bindings x=3, y=x, and z=y become
--    let x1 = 3 in
--    let y1 = x in
--    let z  = y in
--    let x  = x1 in
--    let y  = y1 in ...
-- The extra bindings will be cleaned up by the simplifier.
mkParallelBindings :: InScopeSet
                   -> [(CoreBndr, CoreExpr)] -> CoreExpr -> CoreExpr
mkParallelBindings _ [] body
  = body
mkParallelBindings ins pairs body
  = go ins pairs []
  where
    go _ [] _ = panic "mkParallelBindings"
    go _ins [(bndr, rhs)] rev_renames
      = Let (NonRec bndr rhs) $ foldr add_rename body (reverse rev_renames)
    go ins ((bndr, rhs) : pairs) rev_renames
      | bndr `elemInScopeSet` ins
      = Let (NonRec bndr' rhs) $ go ins' pairs ((bndr, bndr') : rev_renames)
      | otherwise
      = Let (NonRec bndr rhs) $ go ins_w_bndr pairs rev_renames
      where
        bndr'      = zap $ uniqAway ins bndr
        ins'       = extendInScopeSet ins bndr'
        ins_w_bndr = extendInScopeSet ins bndr

    add_rename (bndr, bndr') body
      = Let (NonRec bndr (varToCoreExpr bndr')) body
    zap bndr | isId bndr = zapFragileIdInfo bndr
             | otherwise = bndr

{-
************************************************************************
*                                                                      *
\subsection{Making literals}
*                                                                      *
************************************************************************
-}

-- | Create a 'CoreExpr' which will evaluate to the given @Int@
mkIntExpr :: DynFlags -> Integer -> CoreExpr        -- Result = I# i :: Int
mkIntExpr dflags i = mkCoreConApps intDataCon  [mkIntLit dflags i]

-- | Create a 'CoreExpr' which will evaluate to the given @Int@
mkIntExprInt :: DynFlags -> Int -> CoreExpr         -- Result = I# i :: Int
mkIntExprInt dflags i = mkCoreConApps intDataCon  [mkIntLitInt dflags i]

-- | Create a 'CoreExpr' which will evaluate to the a @Word@ with the given value
mkWordExpr :: DynFlags -> Integer -> CoreExpr
mkWordExpr dflags w = mkCoreConApps wordDataCon [mkWordLit dflags w]

-- | Create a 'CoreExpr' which will evaluate to the given @Word@
mkWordExprWord :: DynFlags -> Word -> CoreExpr
mkWordExprWord dflags w = mkCoreConApps wordDataCon [mkWordLitWord dflags w]

-- | Create a 'CoreExpr' which will evaluate to the given @Integer@
mkIntegerExpr  :: MonadThings m => Integer -> m CoreExpr  -- Result :: Integer
mkIntegerExpr i = do t <- lookupTyCon integerTyConName
                     return (Lit (mkLitInteger i (mkTyConTy t)))

-- | Create a 'CoreExpr' which will evaluate to the given @Float@
mkFloatExpr :: Float -> CoreExpr
mkFloatExpr f = mkCoreConApps floatDataCon [mkFloatLitFloat f]

-- | Create a 'CoreExpr' which will evaluate to the given @Double@
mkDoubleExpr :: Double -> CoreExpr
mkDoubleExpr d = mkCoreConApps doubleDataCon [mkDoubleLitDouble d]


-- | Create a 'CoreExpr' which will evaluate to the given @Char@
mkCharExpr     :: Char             -> CoreExpr      -- Result = C# c :: Int
mkCharExpr c = mkCoreConApps charDataCon [mkCharLit c]

-- | Create a 'CoreExpr' which will evaluate to the given @String@
mkStringExpr   :: MonadThings m => String     -> m CoreExpr  -- Result :: String

-- | Create a 'CoreExpr' which will evaluate to a string morally equivalent to the given @FastString@
mkStringExprFS :: MonadThings m => FastString -> m CoreExpr  -- Result :: String

mkStringExpr str = mkStringExprFS (mkFastString str)

mkStringExprFS str
  | nullFS str
  = return (mkNilExpr charTy)

  | all safeChar chars
  = do unpack_id <- lookupId unpackCStringName
       return (App (Var unpack_id) lit)

  | otherwise
  = do unpack_utf8_id <- lookupId unpackCStringUtf8Name
       return (App (Var unpack_utf8_id) lit)

  where
    chars = unpackFS str
    safeChar c = ord c >= 1 && ord c <= 0x7F
    lit = Lit (MachStr (fastStringToByteString str))

{-
************************************************************************
*                                                                      *
\subsection{Tuple constructors}
*                                                                      *
************************************************************************
-}

{-
Creating tuples and their types for Core expressions

@mkBigCoreVarTup@ builds a tuple; the inverse to @mkTupleSelector@.

* If it has only one element, it is the identity function.

* If there are more elements than a big tuple can have, it nests
  the tuples.

Note [Flattening one-tuples]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This family of functions creates a tuple of variables/expressions/types.
  mkCoreTup [e1,e2,e3] = (e1,e2,e3)
What if there is just one variable/expression/type in the agument?
We could do one of two things:

* Flatten it out, so that
    mkCoreTup [e1] = e1

* Built a one-tuple (see Note [One-tuples] in TysWiredIn)
    mkCoreTup1 [e1] = Unit e1
  We use a suffix "1" to indicate this.

Usually we want the former, but occasionally the latter.
-}

-- | Build a small tuple holding the specified variables
-- One-tuples are flattened; see Note [Flattening one-tuples]
mkCoreVarTup :: [Id] -> CoreExpr
mkCoreVarTup ids = mkCoreTup (map Var ids)

-- | Build the type of a small tuple that holds the specified variables
-- One-tuples are flattened; see Note [Flattening one-tuples]
mkCoreVarTupTy :: [Id] -> Type
mkCoreVarTupTy ids = mkBoxedTupleTy (map idType ids)

-- | Build a small tuple holding the specified expressions
-- One-tuples are flattened; see Note [Flattening one-tuples]
mkCoreTup :: [CoreExpr] -> CoreExpr
mkCoreTup []  = Var unitDataConId
mkCoreTup [c] = c
mkCoreTup cs  = mkCoreConApps (tupleDataCon Boxed (length cs))
                              (map (Type . exprType) cs ++ cs)

-- | Build a small unboxed tuple holding the specified expressions,
-- with the given types. The types must be the types of the expressions.
-- Do not include the RuntimeRep specifiers; this function calculates them
-- for you.
-- Does /not/ flatten one-tuples; see Note [Flattening one-tuples]
mkCoreUbxTup :: [Type] -> [CoreExpr] -> CoreExpr
mkCoreUbxTup tys exps
  = ASSERT( tys `equalLength` exps)
    mkCoreConApps (tupleDataCon Unboxed (length tys))
             (map (Type . getRuntimeRep "mkCoreUbxTup") tys ++ map Type tys ++ exps)

-- | Make a core tuple of the given boxity
mkCoreTupBoxity :: Boxity -> [CoreExpr] -> CoreExpr
mkCoreTupBoxity Boxed   exps = mkCoreTup exps
mkCoreTupBoxity Unboxed exps = mkCoreUbxTup (map exprType exps) exps

-- | Build a big tuple holding the specified variables
-- One-tuples are flattened; see Note [Flattening one-tuples]
mkBigCoreVarTup :: [Id] -> CoreExpr
mkBigCoreVarTup ids = mkBigCoreTup (map Var ids)

mkBigCoreVarTup1 :: [Id] -> CoreExpr
-- Same as mkBigCoreVarTup, but one-tuples are NOT flattened
--                          see Note [Flattening one-tuples]
mkBigCoreVarTup1 [id] = mkCoreConApps (tupleDataCon Boxed 1)
                                      [Type (idType id), Var id]
mkBigCoreVarTup1 ids  = mkBigCoreTup (map Var ids)

-- | Build the type of a big tuple that holds the specified variables
-- One-tuples are flattened; see Note [Flattening one-tuples]
mkBigCoreVarTupTy :: [Id] -> Type
mkBigCoreVarTupTy ids = mkBigCoreTupTy (map idType ids)

-- | Build a big tuple holding the specified expressions
-- One-tuples are flattened; see Note [Flattening one-tuples]
mkBigCoreTup :: [CoreExpr] -> CoreExpr
mkBigCoreTup = mkChunkified mkCoreTup

-- | Build the type of a big tuple that holds the specified type of thing
-- One-tuples are flattened; see Note [Flattening one-tuples]
mkBigCoreTupTy :: [Type] -> Type
mkBigCoreTupTy = mkChunkified mkBoxedTupleTy


{-
************************************************************************
*                                                                      *
\subsection{Tuple destructors}
*                                                                      *
************************************************************************
-}

-- | Builds a selector which scrutises the given
-- expression and extracts the one name from the list given.
-- If you want the no-shadowing rule to apply, the caller
-- is responsible for making sure that none of these names
-- are in scope.
--
-- If there is just one 'Id' in the tuple, then the selector is
-- just the identity.
--
-- If necessary, we pattern match on a \"big\" tuple.
mkTupleSelector, mkTupleSelector1
    :: [Id]         -- ^ The 'Id's to pattern match the tuple against
    -> Id           -- ^ The 'Id' to select
    -> Id           -- ^ A variable of the same type as the scrutinee
    -> CoreExpr     -- ^ Scrutinee
    -> CoreExpr     -- ^ Selector expression

-- mkTupleSelector [a,b,c,d] b v e
--          = case e of v {
--                (p,q) -> case p of p {
--                           (a,b) -> b }}
-- We use 'tpl' vars for the p,q, since shadowing does not matter.
--
-- In fact, it's more convenient to generate it innermost first, getting
--
--        case (case e of v
--                (p,q) -> p) of p
--          (a,b) -> b
mkTupleSelector vars the_var scrut_var scrut
  = mk_tup_sel (chunkify vars) the_var
  where
    mk_tup_sel [vars] the_var = mkSmallTupleSelector vars the_var scrut_var scrut
    mk_tup_sel vars_s the_var = mkSmallTupleSelector group the_var tpl_v $
                                mk_tup_sel (chunkify tpl_vs) tpl_v
        where
          tpl_tys = [mkBoxedTupleTy (map idType gp) | gp <- vars_s]
          tpl_vs  = mkTemplateLocals tpl_tys
          [(tpl_v, group)] = [(tpl,gp) | (tpl,gp) <- zipEqual "mkTupleSelector" tpl_vs vars_s,
                                         the_var `elem` gp ]
-- ^ 'mkTupleSelector1' is like 'mkTupleSelector'
-- but one-tuples are NOT flattened (see Note [Flattening one-tuples])
mkTupleSelector1 vars the_var scrut_var scrut
  | [_] <- vars
  = mkSmallTupleSelector1 vars the_var scrut_var scrut
  | otherwise
  = mkTupleSelector vars the_var scrut_var scrut

-- | Like 'mkTupleSelector' but for tuples that are guaranteed
-- never to be \"big\".
--
-- > mkSmallTupleSelector [x] x v e = [| e |]
-- > mkSmallTupleSelector [x,y,z] x v e = [| case e of v { (x,y,z) -> x } |]
mkSmallTupleSelector, mkSmallTupleSelector1
          :: [Id]        -- The tuple args
          -> Id          -- The selected one
          -> Id          -- A variable of the same type as the scrutinee
          -> CoreExpr    -- Scrutinee
          -> CoreExpr
mkSmallTupleSelector [var] should_be_the_same_var _ scrut
  = ASSERT(var == should_be_the_same_var)
    scrut  -- Special case for 1-tuples
mkSmallTupleSelector vars the_var scrut_var scrut
  = mkSmallTupleSelector1 vars the_var scrut_var scrut

-- ^ 'mkSmallTupleSelector1' is like 'mkSmallTupleSelector'
-- but one-tuples are NOT flattened (see Note [Flattening one-tuples])
mkSmallTupleSelector1 vars the_var scrut_var scrut
  = ASSERT( notNull vars )
    Case scrut scrut_var (idType the_var)
         [(DataAlt (tupleDataCon Boxed (length vars)), vars, Var the_var)]

-- | A generalization of 'mkTupleSelector', allowing the body
-- of the case to be an arbitrary expression.
--
-- To avoid shadowing, we use uniques to invent new variables.
--
-- If necessary we pattern match on a \"big\" tuple.
mkTupleCase :: UniqSupply       -- ^ For inventing names of intermediate variables
            -> [Id]             -- ^ The tuple identifiers to pattern match on
            -> CoreExpr         -- ^ Body of the case
            -> Id               -- ^ A variable of the same type as the scrutinee
            -> CoreExpr         -- ^ Scrutinee
            -> CoreExpr
-- ToDo: eliminate cases where none of the variables are needed.
--
--         mkTupleCase uniqs [a,b,c,d] body v e
--           = case e of v { (p,q) ->
--             case p of p { (a,b) ->
--             case q of q { (c,d) ->
--             body }}}
mkTupleCase uniqs vars body scrut_var scrut
  = mk_tuple_case uniqs (chunkify vars) body
  where
    -- This is the case where don't need any nesting
    mk_tuple_case _ [vars] body
      = mkSmallTupleCase vars body scrut_var scrut

    -- This is the case where we must make nest tuples at least once
    mk_tuple_case us vars_s body
      = let (us', vars', body') = foldr one_tuple_case (us, [], body) vars_s
            in mk_tuple_case us' (chunkify vars') body'

    one_tuple_case chunk_vars (us, vs, body)
      = let (uniq, us') = takeUniqFromSupply us
            scrut_var = mkSysLocal (fsLit "ds") uniq
              (mkBoxedTupleTy (map idType chunk_vars))
            body' = mkSmallTupleCase chunk_vars body scrut_var (Var scrut_var)
        in (us', scrut_var:vs, body')

-- | As 'mkTupleCase', but for a tuple that is small enough to be guaranteed
-- not to need nesting.
mkSmallTupleCase
        :: [Id]         -- ^ The tuple args
        -> CoreExpr     -- ^ Body of the case
        -> Id           -- ^ A variable of the same type as the scrutinee
        -> CoreExpr     -- ^ Scrutinee
        -> CoreExpr

mkSmallTupleCase [var] body _scrut_var scrut
  = bindNonRec var scrut body
mkSmallTupleCase vars body scrut_var scrut
-- One branch no refinement?
  = Case scrut scrut_var (exprType body)
         [(DataAlt (tupleDataCon Boxed (length vars)), vars, body)]

{-
************************************************************************
*                                                                      *
                Floats
*                                                                      *
************************************************************************
-}

data FloatBind
  = FloatLet  CoreBind
  | FloatCase CoreExpr Id AltCon [Var]
      -- case e of y { C ys -> ... }
      -- See Note [Floating cases] in SetLevels

instance Outputable FloatBind where
  ppr (FloatLet b) = text "LET" <+> ppr b
  ppr (FloatCase e b c bs) = hang (text "CASE" <+> ppr e <+> ptext (sLit "of") <+> ppr b)
                                2 (ppr c <+> ppr bs)

wrapFloat :: FloatBind -> CoreExpr -> CoreExpr
wrapFloat (FloatLet defns)       body = Let defns body
wrapFloat (FloatCase e b con bs) body = Case e b (exprType body) [(con, bs, body)]

{-
************************************************************************
*                                                                      *
\subsection{Common list manipulation expressions}
*                                                                      *
************************************************************************

Call the constructor Ids when building explicit lists, so that they
interact well with rules.
-}

-- | Makes a list @[]@ for lists of the specified type
mkNilExpr :: Type -> CoreExpr
mkNilExpr ty = mkCoreConApps nilDataCon [Type ty]

-- | Makes a list @(:)@ for lists of the specified type
mkConsExpr :: Type -> CoreExpr -> CoreExpr -> CoreExpr
mkConsExpr ty hd tl = mkCoreConApps consDataCon [Type ty, hd, tl]

-- | Make a list containing the given expressions, where the list has the given type
mkListExpr :: Type -> [CoreExpr] -> CoreExpr
mkListExpr ty xs = foldr (mkConsExpr ty) (mkNilExpr ty) xs

-- | Make a fully applied 'foldr' expression
mkFoldrExpr :: MonadThings m
            => Type             -- ^ Element type of the list
            -> Type             -- ^ Fold result type
            -> CoreExpr         -- ^ "Cons" function expression for the fold
            -> CoreExpr         -- ^ "Nil" expression for the fold
            -> CoreExpr         -- ^ List expression being folded acress
            -> m CoreExpr
mkFoldrExpr elt_ty result_ty c n list = do
    foldr_id <- lookupId foldrName
    return (Var foldr_id `App` Type elt_ty
           `App` Type result_ty
           `App` c
           `App` n
           `App` list)

-- | Make a 'build' expression applied to a locally-bound worker function
mkBuildExpr :: (MonadThings m, MonadUnique m)
            => Type                                     -- ^ Type of list elements to be built
            -> ((Id, Type) -> (Id, Type) -> m CoreExpr) -- ^ Function that, given information about the 'Id's
                                                        -- of the binders for the build worker function, returns
                                                        -- the body of that worker
            -> m CoreExpr
mkBuildExpr elt_ty mk_build_inside = do
    [n_tyvar] <- newTyVars [alphaTyVar]
    let n_ty = mkTyVarTy n_tyvar
        c_ty = mkFunTys [elt_ty, n_ty] n_ty
    [c, n] <- sequence [mkSysLocalM (fsLit "c") c_ty, mkSysLocalM (fsLit "n") n_ty]

    build_inside <- mk_build_inside (c, c_ty) (n, n_ty)

    build_id <- lookupId buildName
    return $ Var build_id `App` Type elt_ty `App` mkLams [n_tyvar, c, n] build_inside
  where
    newTyVars tyvar_tmpls = do
      uniqs <- getUniquesM
      return (zipWith setTyVarUnique tyvar_tmpls uniqs)

{-
************************************************************************
*                                                                      *
             Manipulating Maybe data type
*                                                                      *
************************************************************************
-}


-- | Makes a Nothing for the specified type
mkNothingExpr :: Type -> CoreExpr
mkNothingExpr ty = mkConApp nothingDataCon [Type ty]

-- | Makes a Just from a value of the specified type
mkJustExpr :: Type -> CoreExpr -> CoreExpr
mkJustExpr ty val = mkConApp justDataCon [Type ty, val]


{-
************************************************************************
*                                                                      *
                      Error expressions
*                                                                      *
************************************************************************
-}

mkRuntimeErrorApp
        :: Id           -- Should be of type (forall a. Addr# -> a)
                        --      where Addr# points to a UTF8 encoded string
        -> Type         -- The type to instantiate 'a'
        -> String       -- The string to print
        -> CoreExpr

mkRuntimeErrorApp err_id res_ty err_msg
  = mkApps (Var err_id) [ Type (getRuntimeRep "mkRuntimeErrorApp" res_ty)
                        , Type res_ty, err_string ]
  where
    err_string = Lit (mkMachString err_msg)

mkImpossibleExpr :: Type -> CoreExpr
mkImpossibleExpr res_ty
  = mkRuntimeErrorApp rUNTIME_ERROR_ID res_ty "Impossible case alternative"

{-
************************************************************************
*                                                                      *
                     Error Ids
*                                                                      *
************************************************************************

GHC randomly injects these into the code.

@patError@ is just a version of @error@ for pattern-matching
failures.  It knows various ``codes'' which expand to longer
strings---this saves space!

@absentErr@ is a thing we put in for ``absent'' arguments.  They jolly
well shouldn't be yanked on, but if one is, then you will get a
friendly message from @absentErr@ (rather than a totally random
crash).

@parError@ is a special version of @error@ which the compiler does
not know to be a bottoming Id.  It is used in the @_par_@ and @_seq_@
templates, but we don't ever expect to generate code for it.
-}

errorIds :: [Id]
errorIds
  = [ rUNTIME_ERROR_ID,
      iRREFUT_PAT_ERROR_ID,
      nON_EXHAUSTIVE_GUARDS_ERROR_ID,
      nO_METHOD_BINDING_ERROR_ID,
      pAT_ERROR_ID,
      rEC_CON_ERROR_ID,
      rEC_SEL_ERROR_ID,
      aBSENT_ERROR_ID,
      tYPE_ERROR_ID   -- Used with Opt_DeferTypeErrors, see #10284
      ]

recSelErrorName, runtimeErrorName, absentErrorName :: Name
irrefutPatErrorName, recConErrorName, patErrorName :: Name
nonExhaustiveGuardsErrorName, noMethodBindingErrorName :: Name
typeErrorName :: Name

recSelErrorName     = err_nm "recSelError"     recSelErrorIdKey     rEC_SEL_ERROR_ID
absentErrorName     = err_nm "absentError"     absentErrorIdKey     aBSENT_ERROR_ID
runtimeErrorName    = err_nm "runtimeError"    runtimeErrorIdKey    rUNTIME_ERROR_ID
irrefutPatErrorName = err_nm "irrefutPatError" irrefutPatErrorIdKey iRREFUT_PAT_ERROR_ID
recConErrorName     = err_nm "recConError"     recConErrorIdKey     rEC_CON_ERROR_ID
patErrorName        = err_nm "patError"        patErrorIdKey        pAT_ERROR_ID
typeErrorName       = err_nm "typeError"       typeErrorIdKey       tYPE_ERROR_ID

noMethodBindingErrorName     = err_nm "noMethodBindingError"
                                  noMethodBindingErrorIdKey nO_METHOD_BINDING_ERROR_ID
nonExhaustiveGuardsErrorName = err_nm "nonExhaustiveGuardsError"
                                  nonExhaustiveGuardsErrorIdKey nON_EXHAUSTIVE_GUARDS_ERROR_ID

err_nm :: String -> Unique -> Id -> Name
err_nm str uniq id = mkWiredInIdName cONTROL_EXCEPTION_BASE (fsLit str) uniq id

rEC_SEL_ERROR_ID, rUNTIME_ERROR_ID, iRREFUT_PAT_ERROR_ID, rEC_CON_ERROR_ID :: Id
pAT_ERROR_ID, nO_METHOD_BINDING_ERROR_ID, nON_EXHAUSTIVE_GUARDS_ERROR_ID :: Id
tYPE_ERROR_ID :: Id
aBSENT_ERROR_ID :: Id
rEC_SEL_ERROR_ID                = mkRuntimeErrorId recSelErrorName
rUNTIME_ERROR_ID                = mkRuntimeErrorId runtimeErrorName
iRREFUT_PAT_ERROR_ID            = mkRuntimeErrorId irrefutPatErrorName
rEC_CON_ERROR_ID                = mkRuntimeErrorId recConErrorName
pAT_ERROR_ID                    = mkRuntimeErrorId patErrorName
nO_METHOD_BINDING_ERROR_ID      = mkRuntimeErrorId noMethodBindingErrorName
nON_EXHAUSTIVE_GUARDS_ERROR_ID  = mkRuntimeErrorId nonExhaustiveGuardsErrorName
aBSENT_ERROR_ID                 = mkRuntimeErrorId absentErrorName
tYPE_ERROR_ID                   = mkRuntimeErrorId typeErrorName

mkRuntimeErrorId :: Name -> Id
-- Error function
--   with type:  forall (r:RuntimeRep) (a:TYPE r). Addr# -> a
--   with arity: 1
-- which diverges after being given one argument
-- The Addr# is expected to be the address of
--   a UTF8-encoded error string
mkRuntimeErrorId name
 = mkVanillaGlobalWithInfo name runtime_err_ty bottoming_info
 where
    bottoming_info = vanillaIdInfo `setStrictnessInfo`    strict_sig
                                   `setArityInfo`         1
                        -- Make arity and strictness agree

        -- Do *not* mark them as NoCafRefs, because they can indeed have
        -- CAF refs.  For example, pAT_ERROR_ID calls GHC.Err.untangle,
        -- which has some CAFs
        -- In due course we may arrange that these error-y things are
        -- regarded by the GC as permanently live, in which case we
        -- can give them NoCaf info.  As it is, any function that calls
        -- any pc_bottoming_Id will itself have CafRefs, which bloats
        -- SRTs.

    strict_sig = mkClosedStrictSig [evalDmd] exnRes
              -- exnRes: these throw an exception, not just diverge

    -- forall (rr :: RuntimeRep) (a :: rr). Addr# -> a
    --   See Note [Error and friends have an "open-tyvar" forall]
    runtime_err_ty = mkSpecSigmaTy [runtimeRep1TyVar, openAlphaTyVar] []
                                   (mkFunTy addrPrimTy openAlphaTy)

{- Note [Error and friends have an "open-tyvar" forall]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
'error' and 'undefined' have types
        error     :: forall (v :: RuntimeRep) (a :: TYPE v). String -> a
        undefined :: forall (v :: RuntimeRep) (a :: TYPE v). a
Notice the runtime-representation polymophism. This ensures that
"error" can be instantiated at unboxed as well as boxed types.
This is OK because it never returns, so the return type is irrelevant.
-}

