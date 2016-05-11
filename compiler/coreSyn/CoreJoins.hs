{-# LANGUAGE CPP #-}

module CoreJoins (findJoinsInPgm, findJoinsInExpr,
  eraseJoins, lintJoinsInCoreBindings,
  SortedBndr(..), BndrSort(..),
  isValBndr, isJoinBndr, asValBndr, asJoinBndr, sbSort, sbBndr, onBndr,
  SortedTyBndr, SortedCoBndr, SortedIdBndr,
  ExprWithJoins, BindWithJoins, AltWithJoins, ProgramWithJoins) where

import CoreSyn
import MonadUtils
import Outputable
import PprCore ()
import Util
import Var
import VarEnv
import VarSet

import Control.Monad

#include "HsVersions.h"

data BndrSort   = ValBndr | JoinBndr deriving (Eq)
data SortedBndr = SB CoreBndr BndrSort deriving (Eq)
  -- Could be TaggedBndr, but shouldn't think of the sort as a tag but as
  -- essential information

type SortedTyBndr = SortedBndr -- must be ValBndr
type SortedCoBndr = SortedBndr -- must be ValBndr
type SortedIdBndr = SortedBndr

instance WrappedBndr SortedBndr where
  unwrapBndr (SB bndr _) = bndr
  rewrapBndr (SB _ sort) bndr = SB bndr sort

isJoinBndr, isValBndr :: SortedBndr -> Bool
isJoinBndr = (== JoinBndr) . sbSort
isValBndr  = (== ValBndr)  . sbSort

asValBndr, asJoinBndr :: CoreBndr -> SortedBndr
asValBndr  id = SB id ValBndr
asJoinBndr id = SB id JoinBndr

sbSort :: SortedBndr -> BndrSort
sbSort (SB _bndr sort) = sort

sbBndr :: SortedBndr -> CoreBndr
sbBndr (SB bndr _sort) = bndr

onBndr :: (CoreBndr -> CoreBndr) -> SortedBndr -> SortedBndr
onBndr f (SB bndr sort) = SB (f bndr) sort

type ExprWithJoins    = Expr SortedBndr
type BindWithJoins    = Bind SortedBndr
type AltWithJoins     = Alt SortedBndr
type ProgramWithJoins = [Bind SortedBndr]

findJoinsInPgm :: CoreProgram -> ProgramWithJoins
findJoinsInPgm pgm = map (\bind -> initFJ $ fjTopBind bind) pgm

findJoinsInExpr :: CoreExpr -> ExprWithJoins
findJoinsInExpr expr = initFJ $ do (expr', anal) <- fjExpr expr
                                   MASSERT(isEmptyJoinAnal anal)
                                   return expr'

eraseJoins :: ProgramWithJoins -> CoreProgram
eraseJoins = map unwrapBndrsInBind -- use WrappedBndr instance

lintJoinsInCoreBindings :: ProgramWithJoins -> ()
lintJoinsInCoreBindings pgm
  = runLintJM $ do mapM_ (lintJBind emptyJoinVarSets) pgm
                   return ()

-------------------------
-- Finding join points --
-------------------------

fjTopBind :: CoreBind -> FJM BindWithJoins 
fjTopBind (NonRec bndr expr)
  = do (bndr', expr') <- fjTopPair (bndr, expr)
       return $ NonRec bndr' expr'
fjTopBind (Rec pairs)
  = Rec <$> (mapM fjTopPair pairs)

fjTopPair :: (CoreBndr, CoreExpr) -> FJM (SortedBndr, ExprWithJoins)
fjTopPair (bndr, expr)
  = do (expr', _) <- fjExpr expr
       return (SB bndr ValBndr, expr') -- can't have top-level join

fjExpr :: CoreExpr -> FJM (ExprWithJoins, JoinAnal)
fjExpr (Lit l)       = return (Lit l, emptyJoinAnal)
fjExpr (Coercion co) = return (Coercion co, emptyJoinAnal)
fjExpr (Type ty)     = return (Type ty, emptyJoinAnal)

fjExpr (Var v)
  = fjApp v []
fjExpr expr@(App {})
  | Var v <- fun
  = fjApp v args
  | otherwise
  = do (fun', fun_anal)   <- fjExpr fun
       (args', arg_anals) <- mapAndUnzipM fjExpr args
       return (mkApps fun' args',
                markAllVarsBad $ combineManyJoinAnals (fun_anal : arg_anals))
  where
    (fun, args) = collectArgs expr
fjExpr expr@(Lam {})
  = do let (bndrs, body) = collectBinders expr
       (body', anal) <- withoutCandidatesFJ bndrs $ fjExpr body
       return (mkLams [ SB bndr ValBndr | bndr <- bndrs ] body', markAllVarsBad anal)
fjExpr (Let bind body)
  = do (expr', anal, _)
         <- mfix $ \ ~(_, _, sort) ->
                     fjLet sort bind body
       return (expr', anal)
fjExpr (Case scrut bndr ty alts)
  = do (scrut', scrut_anal) <- fjExpr scrut
       (alts', alt_anals) <- withoutCandidatesFJ [bndr] $ mapAndUnzipM fjAlt alts
       let anal = combineManyJoinAnals (markAllVarsBad scrut_anal : alt_anals)
       return (Case scrut' (SB bndr ValBndr) ty alts', anal)
fjExpr (Cast expr co)
  = do (expr', anal) <- fjExpr expr
       return (Cast expr' co, markAllVarsBad anal)
fjExpr (Tick ti expr)
  = do (expr', anal) <- fjExpr expr
       return (Tick ti expr', markAllVarsBad anal)

fjApp :: Id -> [CoreArg] -> FJM (ExprWithJoins, JoinAnal)
fjApp v args
  = do (args', arg_anals) <- mapAndUnzipM fjExpr args
       m_total_arity <- lookupCandidateFJ v
       let anal = this_anal (length args) m_total_arity
           full_anal = combineManyJoinAnals (anal : map markAllVarsBad arg_anals)
       return (mkApps (Var v) args', full_anal)
  where
    this_anal _ Nothing = emptyJoinAnal
    this_anal n_args (Just total_arity)
      | n_args == total_arity = oneGoodId v
      | otherwise             = oneBadId v

fjLet :: BndrSort -> CoreBind -> CoreExpr -> FJM (ExprWithJoins, JoinAnal, BndrSort)
fjLet rec_sort bind body
  = do (bind', bind_anal, body', body_anal)
         <- do (bind', bind_anal, env_ext)
                 <- vars_bind rec_sort bind
               -- Do the body
               withCandidatesFJ env_ext $ do
                 (body', body_anal) <- fjExpr body

                 return (bind', bind_anal, body', body_anal)
       let new_let = Let bind' body'
           
           real_bind_anal | rec_sort == JoinBndr = bind_anal
                          | otherwise            = markAllVarsBad bind_anal
                              -- Everything escapes which is free in the bindings
           
           real_bind_anal_wo_binders
             | is_rec    = real_bind_anal `removeAllFromJoinAnal` binders
             | otherwise = real_bind_anal
           
           let_anal = (body_anal `removeAllFromJoinAnal` binders)
                        `combineJoinAnals` real_bind_anal_wo_binders

           all_anal | is_rec    = bind_anal `combineJoinAnals` body_anal    -- Still includes binders of
                    | otherwise = body_anal                                 -- this let(rec)

           sort | binders `allInGoodSet` all_anal
                = JoinBndr
                | otherwise
                = ValBndr

       return (
           new_let,
           let_anal,
           sort
         )
  where
    binders        = bindersOf bind
    is_rec         = case bind of NonRec {} -> False; _ -> True

    mk_binding binder rhs
        = (binder, lambdaCount rhs)

    vars_bind :: BndrSort                   -- Whether binding is join point
              -> CoreBind
              -> FJM (BindWithJoins,
                      JoinAnal,            -- free vars; good vars
                      [(Id, TotalArity)])  -- extension to environment

    vars_bind sort (NonRec binder rhs) = do
        (rhs', bind_anal) <- fjRhs rhs
        let
            env_ext_item = mk_binding binder rhs

        return (NonRec (SB binder sort) rhs',
                bind_anal, [env_ext_item])


    vars_bind sort (Rec pairs)
      = let
          (binders, rhss) = unzip pairs
          env_ext = [ mk_binding b rhs
                    | (b,rhs) <- pairs ]
        in
        withCandidatesFJ env_ext $ do
          (rhss', anals)
            <- mapAndUnzipM fjRhs rhss
          let
            anal = combineManyJoinAnals anals

          return (Rec ([ SB bndr sort | bndr <- binders] `zip` rhss'),
                  anal, env_ext)

fjRhs :: CoreExpr -> FJM (ExprWithJoins, JoinAnal)
fjRhs expr = do let (bndrs, body) = collectBinders expr
                (body', anal) <- withoutCandidatesFJ bndrs $ fjExpr body
                return (mkLams [ SB bndr ValBndr | bndr <- bndrs ] body', anal)

fjAlt :: CoreAlt -> FJM (AltWithJoins, JoinAnal)
fjAlt (con, bndrs, rhs)
  = do (rhs', anal) <- withoutCandidatesFJ bndrs $ fjExpr rhs
       return ((con, [ SB bndr ValBndr | bndr <- bndrs ], rhs'), anal)

-- ---------------------------------------------------------------------------
-- Monad
-- ---------------------------------------------------------------------------

-- There's a lot of stuff to pass around, so we use this FJM monad to
-- help.  All the stuff here is only passed *down*.

newtype FJM a = FJM
    { unFJM :: CandSet
            -> a
    }

type TotalArity = Int -- Counting types AND values
type CandSet    = IdEnv TotalArity

initFJ :: FJM a -> a
initFJ m = unFJM m emptyVarEnv

{-# INLINE thenFJ #-}
{-# INLINE returnFJ #-}

returnFJ :: a -> FJM a
returnFJ e = FJM $ \_ -> e

thenFJ :: FJM a -> (a -> FJM b) -> FJM b
thenFJ m k = FJM $ \env
  -> unFJM (k (unFJM m env)) env

instance Functor FJM where
    fmap = liftM

instance Applicative FJM where
    pure = returnFJ
    (<*>) = ap

instance Monad FJM where
    (>>=)  = thenFJ

instance MonadFix FJM where
    mfix expr = FJM $ \env ->
                      let result = unFJM (expr result) env
                      in  result

-- Functions specific to this monad:

withCandidatesFJ :: [(Id, Int)] -> FJM a -> FJM a
withCandidatesFJ ids_w_arity expr
   =    FJM $   \env
   -> unFJM expr (extendVarEnvList env ids_w_arity)

withoutCandidatesFJ :: [Id] -> FJM a -> FJM a
withoutCandidatesFJ ids expr
   =    FJM $   \env
   -> unFJM expr (delVarEnvList env ids)

lookupCandidateFJ :: Id -> FJM (Maybe TotalArity)
lookupCandidateFJ v = FJM $ \env -> lookupVarEnv env v

-- ---------------------------------------------------------------------------
-- Join Analyses
-- ---------------------------------------------------------------------------

type JoinAnal = (GoodSet, BadSet)
type GoodSet = IdSet
type BadSet = IdSet

emptyJoinAnal :: JoinAnal
emptyJoinAnal = (emptyVarSet, emptyVarSet)

isEmptyJoinAnal :: JoinAnal -> Bool
isEmptyJoinAnal (good, bad) = isEmptyVarSet good && isEmptyVarSet bad

oneGoodId :: Id -> JoinAnal
oneGoodId id = (unitVarSet id, emptyVarSet)

oneBadId :: Id -> JoinAnal
oneBadId id = (emptyVarSet, unitVarSet id)

combineJoinAnals :: JoinAnal -> JoinAnal -> JoinAnal
combineJoinAnals (good1, bad1) (good2, bad2)
  = (good, bad)
  where
    good = (good1 `minusVarSet` bad2) `unionVarSet`
           (good2 `minusVarSet` bad1)
    bad  = bad1 `unionVarSet` bad2

combineManyJoinAnals :: [JoinAnal] -> JoinAnal
combineManyJoinAnals []     = emptyJoinAnal
combineManyJoinAnals (a:as) = foldr combineJoinAnals a as
    
markAllVarsBad :: JoinAnal -> JoinAnal
markAllVarsBad (good, bad) = (emptyVarSet, good `unionVarSet` bad)

removeFromJoinAnal :: JoinAnal -> Id -> JoinAnal
removeFromJoinAnal (good, bad) id
  = (good `delVarSet` id, bad `delVarSet` id)

removeAllFromJoinAnal :: JoinAnal -> [Id] -> JoinAnal
removeAllFromJoinAnal (good, bad) ids
  = (good `delVarSetList` ids, bad `delVarSetList` ids)

inGoodSet :: Id -> JoinAnal -> Bool
inGoodSet id (good, _bad) = id `elemVarSet` good

allInGoodSet :: [Id] -> JoinAnal -> Bool
allInGoodSet ids (good, _bad) = isEmptyVarSet (mkVarSet ids `minusVarSet` good)

-- ---------------------------------------------------------------------------
-- Lint
-- ---------------------------------------------------------------------------

type JoinVarSet = VarEnv TotalArity
type JoinVarSets = (JoinVarSet, JoinVarSet) -- in-scope joins, out-of-scope joins
newtype LintJM a = LintJM a
  -- Just for seq; TODO gather errors rather than panicking

instance Applicative LintJM where
  pure = LintJM
  (<*>) = ap
instance Monad LintJM where
  return = pure
  LintJM a >>= k = a `seq` k a
instance Functor LintJM where fmap = liftM

runLintJM :: LintJM a -> a
runLintJM (LintJM a) = a

emptyJoinVarSets :: JoinVarSets
emptyJoinVarSets = (emptyVarEnv, emptyVarEnv)

addBndrs :: [(CoreBndr, TotalArity)] -> JoinVarSets -> JoinVarSets
addBndrs bndrs (ins, outs)
  = (extendVarEnvList ins bndrs, outs)

markAllOut :: JoinVarSets -> JoinVarSets
markAllOut (ins, outs) = (emptyVarEnv, ins `plusVarEnv` outs)

lintJBind :: JoinVarSets -> BindWithJoins -> LintJM JoinVarSets
lintJBind joins (NonRec (SB _ ValBndr) rhs)
  = lintJExpr (markAllOut joins) rhs >> return joins
lintJBind joins (NonRec (SB bndr JoinBndr) rhs)
  = lintJExpr joins rhsBody >> return bodyJoins
  where
    (argBndrs, rhsBody) = collectBinders rhs
    bodyJoins = addBndrs [(bndr, length argBndrs)] joins
lintJBind joins (Rec pairs)
  = mapM_ doPair pairs >> return joins'
  where
    joins' = addBndrs [ (bndr, lambdaCount rhs)
                      | (SB bndr JoinBndr, rhs) <- pairs ] joins
      
    doPair (bndr, rhs) | isJoinBndr bndr = lintJExpr joins' (skip_lambdas rhs)
                       | otherwise = lintJExpr (markAllOut joins') rhs
    
    skip_lambdas expr = snd $ collectBinders expr

lintJExpr :: JoinVarSets -> ExprWithJoins -> LintJM ()
lintJExpr joins (Var v) = lintJApp joins v []
lintJExpr _ (Lit _) = return ()
lintJExpr joins expr@(App {})
  | Var v <- fun
  = lintJApp joins v args
  | otherwise
  = lintJExpr joins' fun >> mapM_ (lintJExpr joins') args
  where
    (fun, args) = collectArgs expr
    joins' = markAllOut joins
lintJExpr joins (Lam bndr expr) = do lintJArgBndr bndr
                                     lintJExpr (markAllOut joins) expr
lintJExpr joins (Let bind body) = do joins' <- lintJBind joins bind
                                     lintJExpr joins' body
lintJExpr joins (Case scrut bndr _ty alts)
  = do lintJExpr (markAllOut joins) scrut
       lintJArgBndr bndr
       mapM_ (lintJAlt joins) alts
lintJExpr joins (Cast expr _) = lintJExpr (markAllOut joins) expr
lintJExpr joins (Tick _ expr) = lintJExpr (markAllOut joins) expr
lintJExpr _ (Type _) = return ()
lintJExpr _ (Coercion _) = return ()

lintJAlt :: JoinVarSets -> AltWithJoins -> LintJM ()
lintJAlt joins (_con, bndrs, rhs)
  = do mapM_ lintJArgBndr bndrs
       lintJExpr joins rhs

lintJApp :: JoinVarSets -> Var -> [ExprWithJoins] -> LintJM ()
lintJApp joins@(ins, outs) v args
  | v `elemVarEnv` outs
  = pprPanic "lintJApp" $
      text "Join var not in scope:" <+> ppr v $$
      text "Scopes:" <+> pprScopes joins
  | Just arity <- lookupVarEnv ins v
  , let call_arity = length args
  , arity /= call_arity
  = pprPanic "lintJApp" $
      text "Arity mismatch calling:" <+> ppr v $$
      text "Expected:" <+> int arity $$
      text "Actual:" <+> int call_arity
  | otherwise
  = mapM_ (lintJExpr (markAllOut joins)) args

lintJArgBndr :: SortedBndr -> LintJM ()
lintJArgBndr (SB bndr JoinBndr)
  = pprPanic "lintJArgBndr" $ text "Unexpected join binder:" <+> ppr bndr
lintJArgBndr _
  = return ()

pprScopes :: JoinVarSets -> SDoc
pprScopes (ins, outs) = text "In:"  <+> ppr ins $$
                        text "Out:" <+> ppr outs

-- ---------------------------------------------------------------------------
-- Misc.
-- ---------------------------------------------------------------------------

lambdaCount :: Expr a -> TotalArity
-- ^ lambdaCount sees how many leading lambdas there are,
--   *not* skipping casts and *counting* type lambdas. We just need to knew
--   whether a given application is total (*including* all type arguments)
lambdaCount expr = length bndrs where (bndrs, _) = collectBinders expr

instance Outputable BndrSort where
  ppr ValBndr  = text "val"
  ppr JoinBndr = text "join"

instance Outputable SortedBndr where
  ppr (SB bndr sort)
    | isTyVar bndr = ppr bndr
    | otherwise    = ppr sort <+> ppr bndr

instance OutputableBndr SortedBndr where
  pprBndr LetBind (SB bndr sort)
    | isTyVar bndr             = pprBndr LetBind bndr
    | otherwise                = ppr sort <+> pprBndr LetBind bndr
  pprBndr site (SB bndr _sort) = pprBndr site bndr
  
  pprInfixOcc (SB bndr _) = pprInfixOcc bndr
  pprPrefixOcc (SB bndr _) = pprInfixOcc bndr