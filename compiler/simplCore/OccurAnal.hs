{-
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998

************************************************************************
*                                                                      *
\section[OccurAnal]{Occurrence analysis pass}
*                                                                      *
************************************************************************

The occurrence analyser re-typechecks a core expression, returning a new
core expression with (hopefully) improved usage information.
-}

{-# LANGUAGE CPP, BangPatterns, MultiWayIf #-}

module OccurAnal (
        occurAnalysePgm, occurAnalyseExpr, occurAnalyseExpr_NoBinderSwap
    ) where

#include "HsVersions.h"

import CoreSyn
import CoreFVs
import CoreUtils        ( exprIsTrivial, isDefaultAlt, isExpandableApp,
                          stripTicksTopE, mkTicks, tryEtaReduce )
import Id
import IdInfo
import Name( localiseName )
import BasicTypes
import Module( Module )
import Coercion
import Type

import VarSet
import VarEnv
import Var
import Demand           ( argOneShots, argsOneShots )
import Digraph          ( SCC(..), Node
                        , stronglyConnCompFromEdgedVerticesUniq
                        , stronglyConnCompFromEdgedVerticesUniqR )
import Unique
import UniqFM
import Util
import Outputable
import Data.List
import Control.Arrow    ( second )

{-
************************************************************************
*                                                                      *
    occurAnalysePgm, occurAnalyseExpr, occurAnalyseExpr_NoBinderSwap
*                                                                      *
************************************************************************

Here's the externally-callable interface:
-}

occurAnalysePgm :: Module       -- Used only in debug output
                -> (Activation -> Bool)
                -> [CoreRule] -> [CoreVect] -> VarSet
                -> CoreProgram -> CoreProgram
occurAnalysePgm this_mod active_rule imp_rules vects vectVars binds
  | isEmptyDetails final_usage
  = occ_anald_binds

  | otherwise   -- See Note [Glomming]
  = WARN( True, hang (text "Glomming in" <+> ppr this_mod <> colon)
                   2 (ppr final_usage) )
    occ_anald_glommed_binds
  where
    init_env = initOccEnv active_rule

    (final_usage, occ_anald_binds) = go init_env binds
    (_, occ_anald_glommed_binds)   = occAnalRecBind init_env TopLevel
                                                    imp_rule_edges
                                                    (flattenBinds occ_anald_binds)
                                                    initial_uds
          -- It's crucial to re-analyse the glommed-together bindings
          -- so that we establish the right loop breakers. Otherwise
          -- we can easily create an infinite loop (Trac #9583 is an example)

    initial_uds = addManyOccsSet emptyDetails
                            (rulesFreeVars imp_rules `unionVarSet`
                             vectsFreeVars vects `unionVarSet`
                             vectVars)
    -- The RULES and VECTORISE declarations keep things alive! (For VECTORISE declarations,
    -- we only get them *until* the vectoriser runs. Afterwards, these dependencies are
    -- reflected in 'vectors' — see Note [Vectorisation declarations and occurrences].)

    -- Note [Preventing loops due to imported functions rules]
    imp_rule_edges = foldr (plusVarEnv_C unionVarSet) emptyVarEnv
                            [ mapVarEnv (const maps_to) (exprFreeIds arg `delVarSetList` ru_bndrs imp_rule)
                            | imp_rule <- imp_rules
                            , not (isBuiltinRule imp_rule)  -- See Note [Plugin rules]
                            , let maps_to = exprFreeIds (ru_rhs imp_rule)
                                             `delVarSetList` ru_bndrs imp_rule
                            , arg <- ru_args imp_rule ]

    go :: OccEnv -> [CoreBind] -> (UsageDetails, [CoreBind])
    go _ []
        = (initial_uds, [])
    go env (bind:binds)
        = (final_usage, bind' ++ binds')
        where
           (bs_usage, binds')   = go env binds
           (final_usage, bind') = occAnalBind env TopLevel imp_rule_edges bind
                                              bs_usage

occurAnalyseExpr :: CoreExpr -> CoreExpr
        -- Do occurrence analysis, and discard occurrence info returned
occurAnalyseExpr = occurAnalyseExpr' True -- do binder swap

occurAnalyseExpr_NoBinderSwap :: CoreExpr -> CoreExpr
occurAnalyseExpr_NoBinderSwap = occurAnalyseExpr' False -- do not do binder swap

occurAnalyseExpr' :: Bool -> CoreExpr -> CoreExpr
occurAnalyseExpr' enable_binder_swap expr
  = snd (occAnal env expr)
  where
    env = (initOccEnv all_active_rules) {occ_binder_swap = enable_binder_swap}
    -- To be conservative, we say that all inlines and rules are active
    all_active_rules = \_ -> True

{- Note [Plugin rules]
~~~~~~~~~~~~~~~~~~~~~~
Conal Elliott (Trac #11651) built a GHC plugin that added some
BuiltinRules (for imported Ids) to the mg_rules field of ModGuts, to
do some domain-specific transformations that could not be expressed
with an ordinary pattern-matching CoreRule.  But then we can't extract
the dependencies (in imp_rule_edges) from ru_rhs etc, because a
BuiltinRule doesn't have any of that stuff.

So we simply assume that BuiltinRules have no dependencies, and filter
them out from the imp_rule_edges comprehension.
-}

{-
************************************************************************
*                                                                      *
                Bindings
*                                                                      *
************************************************************************

Note [Recursive bindings: the grand plan]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When we come across a binding group
  Rec { x1 = r1; ...; xn = rn }
we treat it like this (occAnalRecBind):

1. Occurrence-analyse each right hand side, and build a
   "Details" for each binding to capture the results.

   Wrap the details in a Node (details, node-id, dep-node-ids),
   where node-id is just the unique of the binder, and
   dep-node-ids lists all binders on which this binding depends.
   We'll call these the "scope edges".
   See Note [Forming the Rec groups].

   All this is done by makeNode.

2. Do SCC-analysis on these Nodes.  Each SCC will become a new Rec or
   NonRec.  The key property is that every free variable of a binding
   is accounted for by the scope edges, so that when we are done
   everything is still in scope.

3. For each Cyclic SCC of the scope-edge SCC-analysis in (2), we
   identify suitable loop-breakers to ensure that inlining terminates.
   This is done by occAnalRec.

4. To do so we form a new set of Nodes, with the same details, but
   different edges, the "loop-breaker nodes". The loop-breaker nodes
   have both more and fewer depedencies than the scope edges
   (see Note [Choosing loop breakers])

   More edges: if f calls g, and g has an active rule that mentions h
               then we add an edge from f -> h

   Fewer edges: we only include dependencies on active rules, on rule
                RHSs (not LHSs) and if there is an INLINE pragma only
                on the stable unfolding (and vice versa).  The scope
                edges must be much more inclusive.

5.  The "weak fvs" of a node are, by definition:
       the scope fvs - the loop-breaker fvs
    See Note [Weak loop breakers], and the nd_weak field of Details

6.  Having formed the loop-breaker nodes

Note [Dead code]
~~~~~~~~~~~~~~~~
Dropping dead code for a cyclic Strongly Connected Component is done
in a very simple way:

        the entire SCC is dropped if none of its binders are mentioned
        in the body; otherwise the whole thing is kept.

The key observation is that dead code elimination happens after
dependency analysis: so 'occAnalBind' processes SCCs instead of the
original term's binding groups.

Thus 'occAnalBind' does indeed drop 'f' in an example like

        letrec f = ...g...
               g = ...(...g...)...
        in
           ...g...

when 'g' no longer uses 'f' at all (eg 'f' does not occur in a RULE in
'g'). 'occAnalBind' first consumes 'CyclicSCC g' and then it consumes
'AcyclicSCC f', where 'body_usage' won't contain 'f'.

------------------------------------------------------------
Note [Forming Rec groups]
~~~~~~~~~~~~~~~~~~~~~~~~~
We put bindings {f = ef; g = eg } in a Rec group if "f uses g"
and "g uses f", no matter how indirectly.  We do a SCC analysis
with an edge f -> g if "f uses g".

More precisely, "f uses g" iff g should be in scope wherever f is.
That is, g is free in:
  a) the rhs 'ef'
  b) or the RHS of a rule for f (Note [Rules are extra RHSs])
  c) or the LHS or a rule for f (Note [Rule dependency info])

These conditions apply regardless of the activation of the RULE (eg it might be
inactive in this phase but become active later).  Once a Rec is broken up
it can never be put back together, so we must be conservative.

The principle is that, regardless of rule firings, every variable is
always in scope.

  * Note [Rules are extra RHSs]
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~
    A RULE for 'f' is like an extra RHS for 'f'. That way the "parent"
    keeps the specialised "children" alive.  If the parent dies
    (because it isn't referenced any more), then the children will die
    too (unless they are already referenced directly).

    To that end, we build a Rec group for each cyclic strongly
    connected component,
        *treating f's rules as extra RHSs for 'f'*.
    More concretely, the SCC analysis runs on a graph with an edge
    from f -> g iff g is mentioned in
        (a) f's rhs
        (b) f's RULES
    These are rec_edges.

    Under (b) we include variables free in *either* LHS *or* RHS of
    the rule.  The former might seems silly, but see Note [Rule
    dependency info].  So in Example [eftInt], eftInt and eftIntFB
    will be put in the same Rec, even though their 'main' RHSs are
    both non-recursive.

  * Note [Rule dependency info]
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~
    The VarSet in a RuleInfo is used for dependency analysis in the
    occurrence analyser.  We must track free vars in *both* lhs and rhs.
    Hence use of idRuleVars, rather than idRuleRhsVars in occAnalBind.
    Why both? Consider
        x = y
        RULE f x = v+4
    Then if we substitute y for x, we'd better do so in the
    rule's LHS too, so we'd better ensure the RULE appears to mention 'x'
    as well as 'v'

  * Note [Rules are visible in their own rec group]
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    We want the rules for 'f' to be visible in f's right-hand side.
    And we'd like them to be visible in other functions in f's Rec
    group.  E.g. in Note [Specialisation rules] we want f' rule
    to be visible in both f's RHS, and fs's RHS.

    This means that we must simplify the RULEs first, before looking
    at any of the definitions.  This is done by Simplify.simplRecBind,
    when it calls addLetIdInfo.

------------------------------------------------------------
Note [Choosing loop breakers]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Loop breaking is surprisingly subtle.  First read the section 4 of
"Secrets of the GHC inliner".  This describes our basic plan.
We avoid infinite inlinings by choosing loop breakers, and
ensuring that a loop breaker cuts each loop.

See also Note [Inlining and hs-boot files] in ToIface, which deals
with a closely related source of infinite loops.

Fundamentally, we do SCC analysis on a graph.  For each recursive
group we choose a loop breaker, delete all edges to that node,
re-analyse the SCC, and iterate.

But what is the graph?  NOT the same graph as was used for Note
[Forming Rec groups]!  In particular, a RULE is like an equation for
'f' that is *always* inlined if it is applicable.  We do *not* disable
rules for loop-breakers.  It's up to whoever makes the rules to make
sure that the rules themselves always terminate.  See Note [Rules for
recursive functions] in Simplify.hs

Hence, if
    f's RHS (or its INLINE template if it has one) mentions g, and
    g has a RULE that mentions h, and
    h has a RULE that mentions f

then we *must* choose f to be a loop breaker.  Example: see Note
[Specialisation rules].

In general, take the free variables of f's RHS, and augment it with
all the variables reachable by RULES from those starting points.  That
is the whole reason for computing rule_fv_env in occAnalBind.  (Of
course we only consider free vars that are also binders in this Rec
group.)  See also Note [Finding rule RHS free vars]

Note that when we compute this rule_fv_env, we only consider variables
free in the *RHS* of the rule, in contrast to the way we build the
Rec group in the first place (Note [Rule dependency info])

Note that if 'g' has RHS that mentions 'w', we should add w to
g's loop-breaker edges.  More concretely there is an edge from f -> g
iff
        (a) g is mentioned in f's RHS `xor` f's INLINE rhs
            (see Note [Inline rules])
        (b) or h is mentioned in f's RHS, and
            g appears in the RHS of an active RULE of h
            or a transitive sequence of active rules starting with h

Why "active rules"?  See Note [Finding rule RHS free vars]

Note that in Example [eftInt], *neither* eftInt *nor* eftIntFB is
chosen as a loop breaker, because their RHSs don't mention each other.
And indeed both can be inlined safely.

Note again that the edges of the graph we use for computing loop breakers
are not the same as the edges we use for computing the Rec blocks.
That's why we compute

- rec_edges          for the Rec block analysis
- loop_breaker_nodes for the loop breaker analysis

  * Note [Finding rule RHS free vars]
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    Consider this real example from Data Parallel Haskell
         tagZero :: Array Int -> Array Tag
         {-# INLINE [1] tagZeroes #-}
         tagZero xs = pmap (\x -> fromBool (x==0)) xs

         {-# RULES "tagZero" [~1] forall xs n.
             pmap fromBool <blah blah> = tagZero xs #-}
    So tagZero's RHS mentions pmap, and pmap's RULE mentions tagZero.
    However, tagZero can only be inlined in phase 1 and later, while
    the RULE is only active *before* phase 1.  So there's no problem.

    To make this work, we look for the RHS free vars only for
    *active* rules. That's the reason for the occ_rule_act field
    of the OccEnv.

  * Note [Weak loop breakers]
    ~~~~~~~~~~~~~~~~~~~~~~~~~
    There is a last nasty wrinkle.  Suppose we have

        Rec { f = f_rhs
              RULE f [] = g

              h = h_rhs
              g = h
              ...more...
        }

    Remember that we simplify the RULES before any RHS (see Note
    [Rules are visible in their own rec group] above).

    So we must *not* postInlineUnconditionally 'g', even though
    its RHS turns out to be trivial.  (I'm assuming that 'g' is
    not choosen as a loop breaker.)  Why not?  Because then we
    drop the binding for 'g', which leaves it out of scope in the
    RULE!

    Here's a somewhat different example of the same thing
        Rec { g = h
            ; h = ...f...
            ; f = f_rhs
              RULE f [] = g }
    Here the RULE is "below" g, but we *still* can't postInlineUnconditionally
    g, because the RULE for f is active throughout.  So the RHS of h
    might rewrite to     h = ...g...
    So g must remain in scope in the output program!

    We "solve" this by:

        Make g a "weak" loop breaker (OccInfo = IAmLoopBreaker True)
        iff g is a "missing free variable" of the Rec group

    A "missing free variable" x is one that is mentioned in an RHS or
    INLINE or RULE of a binding in the Rec group, but where the
    dependency on x may not show up in the loop_breaker_nodes (see
    note [Choosing loop breakers} above).

    A normal "strong" loop breaker has IAmLoopBreaker False.  So

                                    Inline  postInlineUnconditionally
   strong   IAmLoopBreaker False    no      no
   weak     IAmLoopBreaker True     yes     no
            other                   yes     yes

    The **sole** reason for this kind of loop breaker is so that
    postInlineUnconditionally does not fire.  Ugh.  (Typically it'll
    inline via the usual callSiteInline stuff, so it'll be dead in the
    next pass, so the main Ugh is the tiresome complication.)

Note [Rules for imported functions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider this
   f = /\a. B.g a
   RULE B.g Int = 1 + f Int
Note that
  * The RULE is for an imported function.
  * f is non-recursive
Now we
can get
   f Int --> B.g Int      Inlining f
         --> 1 + f Int    Firing RULE
and so the simplifier goes into an infinite loop. This
would not happen if the RULE was for a local function,
because we keep track of dependencies through rules.  But
that is pretty much impossible to do for imported Ids.  Suppose
f's definition had been
   f = /\a. C.h a
where (by some long and devious process), C.h eventually inlines to
B.g.  We could only spot such loops by exhaustively following
unfoldings of C.h etc, in case we reach B.g, and hence (via the RULE)
f.

Note that RULES for imported functions are important in practice; they
occur a lot in the libraries.

We regard this potential infinite loop as a *programmer* error.
It's up the programmer not to write silly rules like
     RULE f x = f x
and the example above is just a more complicated version.

Note [Preventing loops due to imported functions rules]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider:
  import GHC.Base (foldr)

  {-# RULES "filterList" forall p. foldr (filterFB (:) p) [] = filter p #-}
  filter p xs = build (\c n -> foldr (filterFB c p) n xs)
  filterFB c p = ...

  f = filter p xs

Note that filter is not a loop-breaker, so what happens is:
  f =          filter p xs
    = {inline} build (\c n -> foldr (filterFB c p) n xs)
    = {inline} foldr (filterFB (:) p) [] xs
    = {RULE}   filter p xs

We are in an infinite loop.

A more elaborate example (that I actually saw in practice when I went to
mark GHC.List.filter as INLINABLE) is as follows. Say I have this module:
  {-# LANGUAGE RankNTypes #-}
  module GHCList where

  import Prelude hiding (filter)
  import GHC.Base (build)

  {-# INLINABLE filter #-}
  filter :: (a -> Bool) -> [a] -> [a]
  filter p [] = []
  filter p (x:xs) = if p x then x : filter p xs else filter p xs

  {-# NOINLINE [0] filterFB #-}
  filterFB :: (a -> b -> b) -> (a -> Bool) -> a -> b -> b
  filterFB c p x r | p x       = x `c` r
                   | otherwise = r

  {-# RULES
  "filter"     [~1] forall p xs.  filter p xs = build (\c n -> foldr
  (filterFB c p) n xs)
  "filterList" [1]  forall p.     foldr (filterFB (:) p) [] = filter p
   #-}

Then (because RULES are applied inside INLINABLE unfoldings, but inlinings
are not), the unfolding given to "filter" in the interface file will be:
  filter p []     = []
  filter p (x:xs) = if p x then x : build (\c n -> foldr (filterFB c p) n xs)
                           else     build (\c n -> foldr (filterFB c p) n xs

Note that because this unfolding does not mention "filter", filter is not
marked as a strong loop breaker. Therefore at a use site in another module:
  filter p xs
    = {inline}
      case xs of []     -> []
                 (x:xs) -> if p x then x : build (\c n -> foldr (filterFB c p) n xs)
                                  else     build (\c n -> foldr (filterFB c p) n xs)

  build (\c n -> foldr (filterFB c p) n xs)
    = {inline} foldr (filterFB (:) p) [] xs
    = {RULE}   filter p xs

And we are in an infinite loop again, except that this time the loop is producing an
infinitely large *term* (an unrolling of filter) and so the simplifier finally
dies with "ticks exhausted"

Because of this problem, we make a small change in the occurrence analyser
designed to mark functions like "filter" as strong loop breakers on the basis that:
  1. The RHS of filter mentions the local function "filterFB"
  2. We have a rule which mentions "filterFB" on the LHS and "filter" on the RHS

So for each RULE for an *imported* function we are going to add
dependency edges between the *local* FVS of the rule LHS and the
*local* FVS of the rule RHS. We don't do anything special for RULES on
local functions because the standard occurrence analysis stuff is
pretty good at getting loop-breakerness correct there.

It is important to note that even with this extra hack we aren't always going to get
things right. For example, it might be that the rule LHS mentions an imported Id,
and another module has a RULE that can rewrite that imported Id to one of our local
Ids.

Note [Specialising imported functions] (referred to from Specialise)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
BUT for *automatically-generated* rules, the programmer can't be
responsible for the "programmer error" in Note [Rules for imported
functions].  In paricular, consider specialising a recursive function
defined in another module.  If we specialise a recursive function B.g,
we get
         g_spec = .....(B.g Int).....
         RULE B.g Int = g_spec
Here, g_spec doesn't look recursive, but when the rule fires, it
becomes so.  And if B.g was mutually recursive, the loop might
not be as obvious as it is here.

To avoid this,
 * When specialising a function that is a loop breaker,
   give a NOINLINE pragma to the specialised function

Note [Glomming]
~~~~~~~~~~~~~~~
RULES for imported Ids can make something at the top refer to something at the bottom:
        f = \x -> B.g (q x)
        h = \y -> 3

        RULE:  B.g (q x) = h x

Applying this rule makes f refer to h, although f doesn't appear to
depend on h.  (And, as in Note [Rules for imported functions], the
dependency might be more indirect. For example, f might mention C.t
rather than B.g, where C.t eventually inlines to B.g.)

NOTICE that this cannot happen for rules whose head is a
locally-defined function, because we accurately track dependencies
through RULES.  It only happens for rules whose head is an imported
function (B.g in the example above).

Solution:
  - When simplifying, bring all top level identifiers into
    scope at the start, ignoring the Rec/NonRec structure, so
    that when 'h' pops up in f's rhs, we find it in the in-scope set
    (as the simplifier generally expects). This happens in simplTopBinds.

  - In the occurrence analyser, if there are any out-of-scope
    occurrences that pop out of the top, which will happen after
    firing the rule:      f = \x -> h x
                          h = \y -> 3
    then just glom all the bindings into a single Rec, so that
    the *next* iteration of the occurrence analyser will sort
    them all out.   This part happens in occurAnalysePgm.

------------------------------------------------------------
Note [Inline rules]
~~~~~~~~~~~~~~~~~~~
None of the above stuff about RULES applies to Inline Rules,
stored in a CoreUnfolding.  The unfolding, if any, is simplified
at the same time as the regular RHS of the function (ie *not* like
Note [Rules are visible in their own rec group]), so it should be
treated *exactly* like an extra RHS.

Or, rather, when computing loop-breaker edges,
  * If f has an INLINE pragma, and it is active, we treat the
    INLINE rhs as f's rhs
  * If it's inactive, we treat f as having no rhs
  * If it has no INLINE pragma, we look at f's actual rhs


There is a danger that we'll be sub-optimal if we see this
     f = ...f...
     [INLINE f = ..no f...]
where f is recursive, but the INLINE is not. This can just about
happen with a sufficiently odd set of rules; eg

        foo :: Int -> Int
        {-# INLINE [1] foo #-}
        foo x = x+1

        bar :: Int -> Int
        {-# INLINE [1] bar #-}
        bar x = foo x + 1

        {-# RULES "foo" [~1] forall x. foo x = bar x #-}

Here the RULE makes bar recursive; but it's INLINE pragma remains
non-recursive. It's tempting to then say that 'bar' should not be
a loop breaker, but an attempt to do so goes wrong in two ways:
   a) We may get
         $df = ...$cfoo...
         $cfoo = ...$df....
         [INLINE $cfoo = ...no-$df...]
      But we want $cfoo to depend on $df explicitly so that we
      put the bindings in the right order to inline $df in $cfoo
      and perhaps break the loop altogether.  (Maybe this
   b)


Example [eftInt]
~~~~~~~~~~~~~~~
Example (from GHC.Enum):

  eftInt :: Int# -> Int# -> [Int]
  eftInt x y = ...(non-recursive)...

  {-# INLINE [0] eftIntFB #-}
  eftIntFB :: (Int -> r -> r) -> r -> Int# -> Int# -> r
  eftIntFB c n x y = ...(non-recursive)...

  {-# RULES
  "eftInt"  [~1] forall x y. eftInt x y = build (\ c n -> eftIntFB c n x y)
  "eftIntList"  [1] eftIntFB  (:) [] = eftInt
   #-}

Note [Specialisation rules]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider this group, which is typical of what SpecConstr builds:

   fs a = ....f (C a)....
   f  x = ....f (C a)....
   {-# RULE f (C a) = fs a #-}

So 'f' and 'fs' are in the same Rec group (since f refers to fs via its RULE).

But watch out!  If 'fs' is not chosen as a loop breaker, we may get an infinite loop:
  - the RULE is applied in f's RHS (see Note [Self-recursive rules] in Simplify
  - fs is inlined (say it's small)
  - now there's another opportunity to apply the RULE

This showed up when compiling Control.Concurrent.Chan.getChanContents.
-}

------------------------------------------------------------------
--                 occAnalBind
------------------------------------------------------------------

occAnalBind :: OccEnv           -- The incoming OccEnv
            -> TopLevelFlag
            -> ImpRuleEdges
            -> CoreBind
            -> UsageDetails             -- Usage details of scope
            -> (UsageDetails,           -- Of the whole let(rec)
                [CoreBind])

occAnalBind env lvl top_env (NonRec binder rhs) body_usage
  = occAnalNonRecBind env lvl top_env binder rhs body_usage
occAnalBind env lvl top_env (Rec pairs) body_usage
  = occAnalRecBind env lvl top_env pairs body_usage

-----------------
occAnalNonRecBind :: OccEnv -> TopLevelFlag -> ImpRuleEdges -> Var -> CoreExpr
                  -> UsageDetails -> (UsageDetails, [CoreBind])
occAnalNonRecBind env lvl imp_rule_edges binder rhs body_usage
  | isTyVar binder      -- A type let; we don't gather usage info
  = (body_usage, [NonRec binder rhs])

  | not (binder `usedIn` body_usage)    -- It's not mentioned
  = (body_usage, [])

  | otherwise                   -- It's mentioned in the body
  = (body_usage' +++ rhs_usage', [NonRec tagged_binder rhs'])
  where
    make_join = canBecomeJoinPoints lvl NonRecursive body_usage
                  [(binder, rhs)]
    (body_usage', tagged_binder) = tagBinder make_join body_usage binder
    (rhs_usage1, rhs') = occAnalNonRecRhs env tagged_binder rhs
    rhs_usage2 = case occAnalUnfolding env NonRecursive binder of
                   Just unf_usage -> rhs_usage1 +++ unf_usage
                   Nothing        -> rhs_usage1
       -- See Node [Rules, unfoldings, and join points]

    rhs_usage3 = addManyOccsSet rhs_usage2 (idRuleVars binder)
       -- See Note [Rules are extra RHSs] and Note [Rule dependency info]

    rhs_usage4 = maybe rhs_usage3 (addManyOccsSet rhs_usage3) $
                 lookupVarEnv imp_rule_edges binder
       -- See Note [Preventing loops due to imported functions rules]

    rhs_usage' = adjustRhsUsage (willBeJoinId_maybe tagged_binder) NonRecursive
                                rhs' rhs_usage4

-----------------
occAnalRecBind :: OccEnv -> TopLevelFlag -> ImpRuleEdges -> [(Var,CoreExpr)]
               -> UsageDetails -> (UsageDetails, [CoreBind])
occAnalRecBind env lvl imp_rule_edges pairs body_usage
  = foldr (occAnalRec lvl) (body_usage, []) sccs
        -- For a recursive group, we
        --      * occ-analyse all the RHSs
        --      * compute strongly-connected components
        --      * feed those components to occAnalRec
        -- See Note [Recursive bindings: the grand plan]
  where
    sccs :: [SCC Details]
    sccs = {-# SCC "occAnalBind.scc" #-}
           stronglyConnCompFromEdgedVerticesUniq nodes

    nodes :: [LetrecNode]
    nodes = {-# SCC "occAnalBind.assoc" #-}
            map (makeNode env imp_rule_edges bndr_set) pairs

    bndr_set = mkVarSet (map fst pairs)

{-
Node [Rules, unfoldings, and join points]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We don't collect detailed occurrence info from unfoldings, since unfoldings are
often copied (that's the whole point!). But we still need to track tail calls
for the purposes of finding join points.

With rules, things are different. Rules for local bindings are only ever created
by specialisation, and specialising a join point already creates a join point.
It's highly unlikely that a function would be eligible to become a join point
only after it's been specialized. Thus we assume that nothing on the right-hand
side of a rule can be made a join point. This could be relaxed, but at a
considerable cost in complexity.
-}

-----------------------------
occAnalRec :: TopLevelFlag
           -> SCC Details
           -> (UsageDetails, [CoreBind])
           -> (UsageDetails, [CoreBind])

        -- The NonRec case is just like a Let (NonRec ...) above
occAnalRec lvl (AcyclicSCC (ND { nd_bndr = bndr, nd_rhs = rhs
                               , nd_uds = rhs_uds}))
           (body_uds, binds)
  | not (bndr `usedIn` body_uds)
  = (body_uds, binds)           -- See Note [Dead code]

  | otherwise                   -- It's mentioned in the body
  = (body_uds' +++ rhs_uds',
     NonRec tagged_bndr rhs : binds)
  where
    make_join = canBecomeJoinPoints lvl NonRecursive body_uds [(bndr, rhs)]
    (body_uds', tagged_bndr) = tagBinder make_join body_uds bndr
    rhs_uds' = adjustRhsUsage (willBeJoinId_maybe tagged_bndr) NonRecursive
                              rhs rhs_uds

        -- The Rec case is the interesting one
        -- See Note [Recursive bindings: the grand plan]
        -- See Note [Loop breaking]
occAnalRec lvl (CyclicSCC orig_details_s) (body_uds, binds)
  | not (any (`usedIn` body_uds) bndrs) -- NB: look at body_uds, not total_uds
  = (body_uds, binds)                   -- See Note [Dead code]

  | otherwise   -- At this point we always build a single Rec
  = -- pprTrace "occAnalRec" (vcat
    --  [ text "weak_fvs" <+> ppr weak_fvs
    --  , text "tagged details" <+> ppr tagged_details_s
    --  , text "lb nodes" <+> ppr loop_breaker_nodes])
    (final_uds, Rec pairs : binds)

  where
    bndrs    = map nd_bndr orig_details_s
    orig_pairs = [ (nd_bndr nd, nd_rhs nd) | nd <- orig_details_s ]
    bndr_set = mkVarSet bndrs

    ----------------------------
    -- Compute usage details
    orig_total_uds = foldl add_uds body_uds orig_details_s

    make_joins = canBecomeJoinPoints lvl Recursive orig_total_uds orig_pairs
    details_s = map adjust orig_details_s
    total_uds = foldl add_uds body_uds details_s
    final_uds = total_uds `minusDetails` bndr_set
    add_uds usage_so_far nd = usage_so_far +++ nd_uds nd

    adjust nd@(ND { nd_bndr = bndr', nd_rhs = rhs', nd_uds = uds })
      = nd { nd_uds = adjustRhsUsage (will_be_join bndr') Recursive rhs' uds }
    -- Haven't tagged the binders yet, so can't use willBeJoinId_maybe
    will_be_join bndr'
      | make_joins
      , let occ = lookupDetails orig_total_uds bndr'
      , AlwaysTailCalled arity <- tailCallInfo occ
      = Just arity
      | otherwise
      = isJoinId_maybe bndr'

    ------------------------------
        -- See Note [Choosing loop breakers] for loop_breaker_nodes
    loop_breaker_nodes :: [LetrecNode]
    loop_breaker_nodes = mkLoopBreakerNodes make_joins bndr_set total_uds
                                            details_s

    ------------------------------
    weak_fvs :: VarSet
    weak_fvs = mapUnionVarSet nd_weak details_s

    ---------------------------
    -- Now reconstruct the cycle
    pairs :: [(Id,CoreExpr)]
    pairs | isEmptyVarSet weak_fvs = reOrderNodes   0 bndr_set weak_fvs loop_breaker_nodes []
          | otherwise              = loopBreakNodes 0 bndr_set weak_fvs loop_breaker_nodes []
          -- If weak_fvs is empty, the loop_breaker_nodes will include
          -- all the edges in the original scope edges [remember,
          -- weak_fvs is the difference between scope edges and
          -- lb-edges], so a fresh SCC computation would yield a
          -- single CyclicSCC result; and reOrderNodes deals with
          -- exactly that case

------------------------------------------------------------------
--                 Loop breaking
------------------------------------------------------------------

type Binding = (Id,CoreExpr)

loopBreakNodes :: Int
               -> VarSet        -- All binders
               -> VarSet        -- Binders whose dependencies may be "missing"
                                -- See Note [Weak loop breakers]
               -> [LetrecNode]
               -> [Binding]             -- Append these to the end
               -> [Binding]
{-
loopBreakNodes is applied to the list of nodes for a cyclic strongly
connected component (there's guaranteed to be a cycle).  It returns
the same nodes, but
        a) in a better order,
        b) with some of the Ids having a IAmALoopBreaker pragma

The "loop-breaker" Ids are sufficient to break all cycles in the SCC.  This means
that the simplifier can guarantee not to loop provided it never records an inlining
for these no-inline guys.

Furthermore, the order of the binds is such that if we neglect dependencies
on the no-inline Ids then the binds are topologically sorted.  This means
that the simplifier will generally do a good job if it works from top bottom,
recording inlinings for any Ids which aren't marked as "no-inline" as it goes.
-}

-- Return the bindings sorted into a plausible order, and marked with loop breakers.
loopBreakNodes depth bndr_set weak_fvs nodes binds
  = go (stronglyConnCompFromEdgedVerticesUniqR nodes) binds
  where
    go []         binds = binds
    go (scc:sccs) binds = loop_break_scc scc (go sccs binds)

    loop_break_scc scc binds
      = case scc of
          AcyclicSCC node  -> mk_non_loop_breaker weak_fvs node : binds
          CyclicSCC nodes  -> reOrderNodes depth bndr_set weak_fvs nodes binds

----------------------------------
reOrderNodes :: Int -> VarSet -> VarSet -> [LetrecNode] -> [Binding] -> [Binding]
    -- Choose a loop breaker, mark it no-inline,
    -- and call loopBreakNodes on the rest
reOrderNodes _ _ _ []     _     = panic "reOrderNodes"
reOrderNodes _ _ _ [node] binds = mk_loop_breaker node : binds
reOrderNodes depth bndr_set weak_fvs (node : nodes) binds
  = -- pprTrace "reOrderNodes" (text "unchosen" <+> ppr unchosen $$
    --                           text "chosen" <+> ppr chosen_nodes) $
    loopBreakNodes new_depth bndr_set weak_fvs unchosen $
    (map mk_loop_breaker chosen_nodes ++ binds)
  where
    (chosen_nodes, unchosen) = chooseLoopBreaker approximate_lb
                                                 (nd_score (fstOf3 node))
                                                 [node] [] nodes

    approximate_lb = depth >= 2
    new_depth | approximate_lb = 0
              | otherwise      = depth+1
        -- After two iterations (d=0, d=1) give up
        -- and approximate, returning to d=0

mk_loop_breaker :: LetrecNode -> Binding
mk_loop_breaker (ND { nd_bndr = bndr, nd_rhs = rhs}, _, _)
  = (bndr `setIdOccInfo` strongLoopBreaker { occ_tail = tail_info }, rhs)
  where
    tail_info = tailCallInfo (idOccInfo bndr)

mk_non_loop_breaker :: VarSet -> LetrecNode -> Binding
-- See Note [Weak loop breakers]
mk_non_loop_breaker weak_fvs (ND { nd_bndr = bndr, nd_rhs = rhs}, _, _)
  | bndr `elemVarSet` weak_fvs = (setIdOccInfo bndr occ', rhs)
  | otherwise                  = (bndr, rhs)
  where
    occ' = weakLoopBreaker { occ_tail = tail_info }
    tail_info = tailCallInfo (idOccInfo bndr)

----------------------------------
chooseLoopBreaker :: Bool             -- True <=> Too many iterations,
                                      --          so approximate
                  -> NodeScore            -- Best score so far
                  -> [LetrecNode]       -- Nodes with this score
                  -> [LetrecNode]       -- Nodes with higher scores
                  -> [LetrecNode]       -- Unprocessed nodes
                  -> ([LetrecNode], [LetrecNode])
    -- This loop looks for the bind with the lowest score
    -- to pick as the loop  breaker.  The rest accumulate in
chooseLoopBreaker _ _ loop_nodes acc []
  = (loop_nodes, acc)        -- Done

    -- If approximate_loop_breaker is True, we pick *all*
    -- nodes with lowest score, else just one
    -- See Note [Complexity of loop breaking]
chooseLoopBreaker approx_lb loop_sc loop_nodes acc (node : nodes)
  | approx_lb
  , rank sc == rank loop_sc
  = chooseLoopBreaker approx_lb loop_sc (node : loop_nodes) acc nodes

  | sc `betterLB` loop_sc  -- Better score so pick this new one
  = chooseLoopBreaker approx_lb sc [node] (loop_nodes ++ acc) nodes

  | otherwise              -- Worse score so don't pick it
  = chooseLoopBreaker approx_lb loop_sc loop_nodes (node : acc) nodes
  where
    sc = nd_score (fstOf3 node)

{-
Note [Complexity of loop breaking]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The loop-breaking algorithm knocks out one binder at a time, and
performs a new SCC analysis on the remaining binders.  That can
behave very badly in tightly-coupled groups of bindings; in the
worst case it can be (N**2)*log N, because it does a full SCC
on N, then N-1, then N-2 and so on.

To avoid this, we switch plans after 2 (or whatever) attempts:
  Plan A: pick one binder with the lowest score, make it
          a loop breaker, and try again
  Plan B: pick *all* binders with the lowest score, make them
          all loop breakers, and try again
Since there are only a small finite number of scores, this will
terminate in a constant number of iterations, rather than O(N)
iterations.

You might thing that it's very unlikely, but RULES make it much
more likely.  Here's a real example from Trac #1969:
  Rec { $dm = \d.\x. op d
        {-# RULES forall d. $dm Int d  = $s$dm1
                  forall d. $dm Bool d = $s$dm2 #-}

        dInt = MkD .... opInt ...
        dInt = MkD .... opBool ...
        opInt  = $dm dInt
        opBool = $dm dBool

        $s$dm1 = \x. op dInt
        $s$dm2 = \x. op dBool }
The RULES stuff means that we can't choose $dm as a loop breaker
(Note [Choosing loop breakers]), so we must choose at least (say)
opInt *and* opBool, and so on.  The number of loop breakders is
linear in the number of instance declarations.

Note [Loop breakers and INLINE/INLINABLE pragmas]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Avoid choosing a function with an INLINE pramga as the loop breaker!
If such a function is mutually-recursive with a non-INLINE thing,
then the latter should be the loop-breaker.

It's vital to distinguish between INLINE and INLINABLE (the
Bool returned by hasStableCoreUnfolding_maybe).  If we start with
   Rec { {-# INLINABLE f #-}
         f x = ...f... }
and then worker/wrapper it through strictness analysis, we'll get
   Rec { {-# INLINABLE $wf #-}
         $wf p q = let x = (p,q) in ...f...

         {-# INLINE f #-}
         f x = case x of (p,q) -> $wf p q }

Now it is vital that we choose $wf as the loop breaker, so we can
inline 'f' in '$wf'.

Note [DFuns should not be loop breakers]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It's particularly bad to make a DFun into a loop breaker.  See
Note [How instance declarations are translated] in TcInstDcls

We give DFuns a higher score than ordinary CONLIKE things because
if there's a choice we want the DFun to be the non-looop breker. Eg

rec { sc = /\ a \$dC. $fBWrap (T a) ($fCT @ a $dC)

      $fCT :: forall a_afE. (Roman.C a_afE) => Roman.C (Roman.T a_afE)
      {-# DFUN #-}
      $fCT = /\a \$dC. MkD (T a) ((sc @ a $dC) |> blah) ($ctoF @ a $dC)
    }

Here 'sc' (the superclass) looks CONLIKE, but we'll never get to it
if we can't unravel the DFun first.

Note [Constructor applications]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It's really really important to inline dictionaries.  Real
example (the Enum Ordering instance from GHC.Base):

     rec     f = \ x -> case d of (p,q,r) -> p x
             g = \ x -> case d of (p,q,r) -> q x
             d = (v, f, g)

Here, f and g occur just once; but we can't inline them into d.
On the other hand we *could* simplify those case expressions if
we didn't stupidly choose d as the loop breaker.
But we won't because constructor args are marked "Many".
Inlining dictionaries is really essential to unravelling
the loops in static numeric dictionaries, see GHC.Float.

Note [Closure conversion]
~~~~~~~~~~~~~~~~~~~~~~~~~
We treat (\x. C p q) as a high-score candidate in the letrec scoring algorithm.
The immediate motivation came from the result of a closure-conversion transformation
which generated code like this:

    data Clo a b = forall c. Clo (c -> a -> b) c

    ($:) :: Clo a b -> a -> b
    Clo f env $: x = f env x

    rec { plus = Clo plus1 ()

        ; plus1 _ n = Clo plus2 n

        ; plus2 Zero     n = n
        ; plus2 (Succ m) n = Succ (plus $: m $: n) }

If we inline 'plus' and 'plus1', everything unravels nicely.  But if
we choose 'plus1' as the loop breaker (which is entirely possible
otherwise), the loop does not unravel nicely.


@occAnalRhs@ deals with the question of bindings where the Id is marked
by an INLINE pragma.  For these we record that anything which occurs
in its RHS occurs many times.  This pessimistically assumes that ths
inlined binder also occurs many times in its scope, but if it doesn't
we'll catch it next time round.  At worst this costs an extra simplifier pass.
ToDo: try using the occurrence info for the inline'd binder.

[March 97] We do the same for atomic RHSs.  Reason: see notes with loopBreakSCC.
[June 98, SLPJ]  I've undone this change; I don't understand it.  See notes with loopBreakSCC.


************************************************************************
*                                                                      *
                   Making nodes
*                                                                      *
************************************************************************
-}

type ImpRuleEdges = IdEnv IdSet     -- Mapping from FVs of imported RULE LHSs to RHS FVs

noImpRuleEdges :: ImpRuleEdges
noImpRuleEdges = emptyVarEnv

type LetrecNode = Node Unique Details  -- Node comes from Digraph
                                       -- The Unique key is gotten from the Id
data Details
  = ND { nd_bndr :: Id          -- Binder
       , nd_rhs  :: CoreExpr    -- RHS, already occ-analysed

       , nd_uds  :: UsageDetails  -- Usage from RHS, and RULES, and stable unfoldings
                                  -- ignoring phase (ie assuming all are active)
                                  -- See Note [Forming Rec groups]

       , nd_inl  :: IdSet       -- Free variables of
                                --   the stable unfolding (if present and active)
                                --   or the RHS (if not)
                                -- but excluding any RULES
                                -- This is the IdSet that may be used if the Id is inlined

       , nd_weak :: IdSet       -- Binders of this Rec that are mentioned in nd_uds
                                -- but are *not* in nd_inl.  These are the ones whose
                                -- dependencies might not be respected by loop_breaker_nodes
                                -- See Note [Weak loop breakers]

       , nd_active_rule_fvs :: IdSet   -- Free variables of the RHS of active RULES

       , nd_score :: NodeScore
  }

instance Outputable Details where
   ppr nd = text "ND" <> braces
             (sep [ text "bndr =" <+> ppr (nd_bndr nd)
                  , text "uds =" <+> ppr (nd_uds nd)
                  , text "inl =" <+> ppr (nd_inl nd)
                  , text "weak =" <+> ppr (nd_weak nd)
                  , text "rule =" <+> ppr (nd_active_rule_fvs nd)
             ])

-- The NodeScore is compared lexicographically;
--      e.g. lower rank wins regardless of size
type NodeScore = ( Int     -- Rank: lower => more likely to be picked as loop breaker
                 , Int     -- Size of rhs: higher => more likely to be picked as LB
                           -- Maxes out at maxExprSize; we just use it to prioritise
                           -- small functions
                 , Bool )  -- Was it a loop breaker before?
                           -- True => more likely to be picked
                           -- Note [Loop breakers, node scoring, and stability]

rank :: NodeScore -> Int
rank (r, _, _) = r

makeNode :: OccEnv -> ImpRuleEdges -> VarSet
         -> (Var, CoreExpr) -> LetrecNode
-- See Note [Recursive bindings: the grand plan]
makeNode env imp_rule_edges bndr_set (bndr, rhs)
  = (details, varUnique bndr, nonDetKeysUFM node_fvs)
    -- It's OK to use nonDetKeysUFM here as stronglyConnCompFromEdgedVerticesR
    -- is still deterministic with edges in nondeterministic order as
    -- explained in Note [Deterministic SCC] in Digraph.
  where
    details = ND { nd_bndr            = bndr
                 , nd_rhs             = rhs'
                 , nd_uds             = rhs_usage3
                 , nd_inl             = inl_fvs
                 , nd_weak            = node_fvs `minusVarSet` inl_fvs
                 , nd_active_rule_fvs = active_rule_fvs
                 , nd_score           = pprPanic "makeNodeDetails" (ppr bndr) }

    -- Constructing the edges for the main Rec computation
    -- See Note [Forming Rec groups]
    (rhs_usage1, rhs') = occAnalRecRhs env rhs
    rhs_usage2 = addManyOccsSet rhs_usage1 all_rule_fvs
                   -- Note [Rules are extra RHSs]
                   -- Note [Rule dependency info]
    rhs_usage3 = case mb_unf_uds of
                   Just unf_uds -> rhs_usage2 +++ unf_uds
                   Nothing      -> rhs_usage2
    node_fvs = udFreeVars bndr_set rhs_usage3

    -- Finding the free variables of the rules
    is_active = occ_rule_act env :: Activation -> Bool
    rules = filterOut isBuiltinRule (idCoreRules bndr)
    rules_w_fvs :: [(Activation, VarSet)]    -- Find the RHS fvs
    rules_w_fvs = maybe id (\ids -> ((AlwaysActive, ids):)) (lookupVarEnv imp_rule_edges bndr)
                   -- See Note [Preventing loops due to imported functions rules]
                  [ (ru_act rule, fvs)
                  | rule <- rules
                  , let fvs = exprFreeVars (ru_rhs rule)
                              `delVarSetList` ru_bndrs rule
                  , not (isEmptyVarSet fvs) ]
    all_rule_fvs = rule_lhs_fvs `unionVarSet` rule_rhs_fvs
    rule_rhs_fvs = mapUnionVarSet snd rules_w_fvs
    rule_lhs_fvs = mapUnionVarSet (\ru -> exprsFreeVars (ru_args ru)
                                          `delVarSetList` ru_bndrs ru) rules
    active_rule_fvs = unionVarSets [fvs | (a,fvs) <- rules_w_fvs, is_active a]

    -- Finding the usage details of the INLINE pragma (if any)
    mb_unf_uds = occAnalUnfolding env Recursive bndr

    -- Find the "nd_inl" free vars; for the loop-breaker phase
    inl_fvs = case mb_unf_uds of
                Nothing -> udFreeVars bndr_set rhs_usage1 -- No INLINE, use RHS
                Just unf_uds -> udFreeVars bndr_set unf_uds
                      -- We could check for an *active* INLINE (returning
                      -- emptyVarSet for an inactive one), but is_active
                      -- isn't the right thing (it tells about
                      -- RULE activation), so we'd need more plumbing

mkLoopBreakerNodes :: Bool -> VarSet -> UsageDetails -> [Details]
                   -> [LetrecNode]
-- Does three things
--   a) tag each binder with its occurrence info
--   b) add a NodeScore to each node
--   c) make a Node with the right dependency edges for
--      the loop-breaker SCC analysis
mkLoopBreakerNodes make_joins bndr_set total_uds details_s
  = map mk_lb_node details_s
  where
    mk_lb_node nd@(ND { nd_bndr = bndr, nd_rhs = rhs, nd_inl = inl_fvs })
      = (nd', varUnique bndr, nonDetKeysUFM lb_deps)
              -- It's OK to use nonDetKeysUFM here as
              -- stronglyConnCompFromEdgedVerticesR is still deterministic with edges
              -- in nondeterministic order as explained in
              -- Note [Deterministic SCC] in Digraph.
      where
        nd'     = nd { nd_bndr = bndr', nd_score = score }
        bndr'   = snd $ tagBinder make_joins total_uds bndr
        score   = nodeScore bndr bndr' rhs lb_deps
        lb_deps = extendFvs_ rule_fv_env inl_fvs

    rule_fv_env :: IdEnv IdSet
        -- Maps a variable f to the variables from this group
        --      mentioned in RHS of active rules for f
        -- Domain is *subset* of bound vars (others have no rule fvs)
    rule_fv_env = transClosureFV (mkVarEnv init_rule_fvs)
    init_rule_fvs   -- See Note [Finding rule RHS free vars]
      = [ (b, trimmed_rule_fvs)
        | ND { nd_bndr = b, nd_active_rule_fvs = rule_fvs } <- details_s
        , let trimmed_rule_fvs = rule_fvs `intersectVarSet` bndr_set
        , not (isEmptyVarSet trimmed_rule_fvs) ]


------------------------------------------
nodeScore :: Id        -- Binder has old occ-info (just for loop-breaker-ness)
          -> Id        -- Binder with new occ-info
          -> CoreExpr  -- RHS
          -> VarSet    -- Loop-breaker dependencies
          -> NodeScore
nodeScore old_bndr new_bndr bind_rhs lb_deps
  | not (isId old_bndr)     -- A type or cercion variable is never a loop breaker
  = (100, 0, False)

  | old_bndr `elemVarSet` lb_deps  -- Self-recursive things are great loop breakers
  = (0, 0, True)                   -- See Note [Self-recursion and loop breakers]

  | otherwise  -- An Id has an unfolding
  = case id_unfolding of
      DFunUnfolding { df_args = args }
        -- Never choose a DFun as a loop breaker
        -- Note [DFuns should not be loop breakers]
        -> (9, length args, is_lb)

      CoreUnfolding { uf_src = src, uf_tmpl = unf_rhs, uf_guidance = guide }
        | isStableSource src
        -> case guide of
             UnfWhen {}                      -> (6, cheapExprSize unf_rhs, is_lb)
             UnfIfGoodArgs { ug_size = size} -> (3, size,                  is_lb)
             UnfNever                        -> (0, 0,                     is_lb)
              -- See Note [Loop breakers and INLINE/INLINABLE pragmas] for
              -- the 6 vs 3 choice

         -- Note that this case hits /all/ stable unfoldings, so we
         -- never look at 'bind_rhs' for stable unfoldings. That's right, because
         -- 'rhs' is irrelevant for inlining things with a stable unfolding

         -- Data structures are more important than INLINE pragmas
         -- so that dictionary/method recursion unravels

      _ | is_trivial
        -> mk_score 10  -- Practically certain to be inlined
          -- Used to have also: && not (isExportedId bndr)
          -- But I found this sometimes cost an extra iteration when we have
          --      rec { d = (a,b); a = ...df...; b = ...df...; df = d }
          -- where df is the exported dictionary. Then df makes a really
          -- bad choice for loop breaker

        | is_con_app bind_rhs   -- Data types help with cases: Note [Constructor applications]
        -> mk_score 5

        | isOneOcc (idOccInfo new_bndr)
        -> mk_score 2  -- Likely to be inlined

        | canUnfold id_unfolding   -- The Id has some kind of unfolding
        -> mk_score 1

        | otherwise
        -> (0, 0, is_lb)

  where
    mk_score :: Int -> NodeScore
    mk_score rank = (rank, rhs_size, is_lb)

    is_lb    = isStrongLoopBreaker (idOccInfo old_bndr)
    rhs_size = case id_unfolding of
                 CoreUnfolding { uf_guidance = guidance }
                    | UnfIfGoodArgs { ug_size = size } <- guidance
                    -> size
                 _  -> cheapExprSize bind_rhs
    is_trivial | exprIsTrivial bind_rhs          = True
               | let (bndrs, body) = collectBinders bind_rhs
               , Just _ <- tryEtaReduce bndrs body = True
                   -- Join points are always eta-expanded. An otherwise trivial
                   -- one like
                   --   join j x1 x2 x3 = j' x1 x2 x3
                   -- won't pass exprIsTrivial, but we certainly don't want to
                   -- pick it as a loop breaker!
               | otherwise                       = False

    id_unfolding = realIdUnfolding old_bndr
       -- realIdUnfolding: Ignore loop-breaker-ness here because
       -- that is what we are setting!

        -- Checking for a constructor application
        -- Cheap and cheerful; the simplifier moves casts out of the way
        -- The lambda case is important to spot x = /\a. C (f a)
        -- which comes up when C is a dictionary constructor and
        -- f is a default method.
        -- Example: the instance for Show (ST s a) in GHC.ST
        --
        -- However we *also* treat (\x. C p q) as a con-app-like thing,
        --      Note [Closure conversion]
    is_con_app (Var v)    = isConLikeId v
    is_con_app (App f _)  = is_con_app f
    is_con_app (Lam _ e)  = is_con_app e
    is_con_app (Tick _ e) = is_con_app e
    is_con_app _          = False

maxExprSize :: Int
maxExprSize = 20  -- Rather arbitrary

cheapExprSize :: CoreExpr -> Int
-- Maxes out at maxExprSize
cheapExprSize e
  = go 0 e
  where
    go n e | n >= maxExprSize = n
           | otherwise        = go1 n e

    go1 n (Var {})        = n+1
    go1 n (Lit {})        = n+1
    go1 n (Type {})       = n
    go1 n (Coercion {})   = n
    go1 n (Tick _ e)      = go1 n e
    go1 n (Cast e _)      = go1 n e
    go1 n (App f a)       = go (go1 n f) a
    go1 n (Lam b e)
      | isTyVar b         = go1 n e
      | otherwise         = go (n+1) e
    go1 n (Let b e)       = gos (go1 n e) (rhssOfBind b)
    go1 n (Case e _ _ as) = gos (go1 n e) (rhssOfAlts as)

    gos n [] = n
    gos n (e:es) | n >= maxExprSize = n
                 | otherwise        = gos (go1 n e) es

betterLB :: NodeScore -> NodeScore -> Bool
-- If  n1 `betterLB` n2  then choose n1 as the loop breaker
betterLB (rank1, size1, lb1) (rank2, size2, _)
  | rank1 < rank2 = True
  | rank1 > rank2 = False
  | size1 < size2 = False   -- Make the bigger n2 into the loop breaker
  | size1 > size2 = True
  | lb1           = True    -- Tie-break: if n1 was a loop breaker before, choose it
  | otherwise     = False   -- See Note [Loop breakers, node scoring, and stability]

{- Note [Self-recursion and loop breakers]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we have
   rec { f = ...f...g...
       ; g = .....f...   }
then 'f' has to be a loop breaker anyway, so we may as well choose it
right away, so that g can inline freely.

This is really just a cheap hack. Consider
   rec { f = ...g...
       ; g = ..f..h...
      ;  h = ...f....}
Here f or g are better loop breakers than h; but we might accidentally
choose h.  Finding the minimal set of loop breakers is hard.

Note [Loop breakers, node scoring, and stability]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
To choose a loop breaker, we give a NodeScore to each node in the SCC,
and pick the one with the best score (according to 'betterLB').

We need to be jolly careful (Trac #12425, #12234) about the stability
of this choice. Suppose we have

    let rec { f = ...g...g...
            ; g = ...f...f... }
    in
    case x of
      True  -> ...f..
      False -> ..f...

In each iteration of the simplifier the occurrence analyser OccAnal
chooses a loop breaker. Suppose in iteration 1 it choose g as the loop
breaker. That means it is free to inline f.

Suppose that GHC decides to inline f in the branches of the case, but
(for some reason; eg it is not satureated) in the rhs of g. So we get

    let rec { f = ...g...g...
            ; g = ...f...f... }
    in
    case x of
      True  -> ...g...g.....
      False -> ..g..g....

Now suppose that, for some reason, in the next iteraion the occurrence
analyser chooses f as the loop breaker, so it can freely inling g. And
again for some reason the simplifer inlines g at its calls in the case
branches, but not in the RHS of f. Then we get

    let rec { f = ...g...g...
            ; g = ...f...f... }
    in
    case x of
      True  -> ...(...f...f...)...(...f..f..).....
      False -> ..(...f...f...)...(..f..f...)....

You can see where this is going! Each iteration of the simplifier
doubles the number of calls to f or g. No wonder GHC is slow!

(In the particular example in comment:3 of #12425, f and g are the two
mutually recursive fmap instances for CondT and Result. They are both
marked INLINE which, oddly, is why they don't inline in each other's
RHS, because the call there is not saturated.)

The root cause is that we flip-flop on our choice of loop breaker. I
always thought it didn't matter, and indeed for any single iteration
to terminate, it doesn't matter. But when we iterate, it matters a
lot!!

So The Plan is this:
   If there is a tie, choose the node that
   was a loop breaker last time round

Hence the is_lb field of NodeScore

************************************************************************
*                                                                      *
                   Right hand sides
*                                                                      *
************************************************************************
-}

occAnalRecRhs :: OccEnv -> CoreExpr    -- Rhs
           -> (UsageDetails, CoreExpr)
              -- Returned usage details covers only the RHS,
              -- and *not* the RULE or INLINE template for the Id
occAnalRecRhs env rhs = occAnalRhs (rhsCtxt env) rhs

occAnalNonRecRhs :: OccEnv
                 -> Id -> CoreExpr    -- Binder and rhs
                     -- Binder is already tagged with occurrence info
                 -> (UsageDetails, CoreExpr)
              -- Returned usage details covers only the RHS,
              -- and *not* the RULE or INLINE template for the Id
occAnalNonRecRhs env bndr rhs
  = occAnalRhs rhs_env rhs
  where
    -- See Note [Cascading inlines]
    env1 | certainly_inline = env
         | otherwise        = rhsCtxt env

    -- See Note [Use one-shot info]
    rhs_env = env1 { occ_one_shots = argOneShots OneShotLam dmd }


    certainly_inline -- See Note [Cascading inlines]
      = case idOccInfo bndr of
          OneOcc { occ_in_lam = in_lam, occ_one_br = one_br }
                                 -> not in_lam && one_br && active && not_stable
          _                      -> False

    dmd        = idDemandInfo bndr
    active     = isAlwaysActive (idInlineActivation bndr)
    not_stable = not (isStableUnfolding (idUnfolding bndr))

-- | Not to be called directly; go through occAnalNonRecRhs or occAnalRecRhs
occAnalRhs :: OccEnv
           -> CoreExpr
           -> (UsageDetails, CoreExpr)
occAnalRhs env expr
  = -- This is somewhat touchy for finding join points. When analyzing a join
    -- point, we want to skip the lambdas, since the body of the join point is
    -- a tail context (i.e. a place where tail calls can occur). But we could be
    -- looking at something that's not a join point *yet*! Fortunately, we
    -- needn't worry about this here; at the let, we'll decide and then know
    -- whether to throw out the tail-call info or not, so for now just leave it
    -- all there.
    --
    -- Thus the game plan is to act largely like occAnal of Lam. However, we
    -- can't yet decide whether to apply markAllInsideLam, since that depends on
    -- on whether this is a join point - lambdas get marked iff they're
    -- one-shot, and a join point is one-shot iff it's non-recursive. So we
    -- defer that decision to the binding site as well.
    case occAnalLam env bndrs body of { (usage, bndrs', body') ->
    (usage, mkLams bndrs' body') }
  where
    (bndrs, body) = collectBinders expr

occAnalUnfolding :: OccEnv
                 -> RecFlag
                 -> Id
                 -> Maybe UsageDetails
                      -- Just the analysis, not a new unfolding. The unfolding
                      -- got analysed when it was created and we don't need to
                      -- update it.
occAnalUnfolding env rec_flag id
  = case realIdUnfolding id of -- ignore previous loop-breaker flag
      CoreUnfolding { uf_tmpl = rhs, uf_src = src }
        | not (isStableSource src)
        -> Nothing
        | otherwise
        -> Just $ zapDetails usage
        where
          (usage, _rhs') | isRec rec_flag = occAnalRecRhs env rhs
                         | otherwise      = occAnalNonRecRhs env id rhs

      DFunUnfolding { df_bndrs = bndrs, df_args = args }
        -> Just $ zapDetails (delDetailsList usage bndrs)
        where
          usage = foldr (+++) emptyDetails (map (fst . occAnal env) args)

      _ -> Nothing

{-
Note [Cascading inlines]
~~~~~~~~~~~~~~~~~~~~~~~~
By default we use an rhsCtxt for the RHS of a binding.  This tells the
occ anal n that it's looking at an RHS, which has an effect in
occAnalApp.  In particular, for constructor applications, it makes
the arguments appear to have NoOccInfo, so that we don't inline into
them. Thus    x = f y
              k = Just x
we do not want to inline x.

But there's a problem.  Consider
     x1 = a0 : []
     x2 = a1 : x1
     x3 = a2 : x2
     g  = f x3
First time round, it looks as if x1 and x2 occur as an arg of a
let-bound constructor ==> give them a many-occurrence.
But then x3 is inlined (unconditionally as it happens) and
next time round, x2 will be, and the next time round x1 will be
Result: multiple simplifier iterations.  Sigh.

So, when analysing the RHS of x3 we notice that x3 will itself
definitely inline the next time round, and so we analyse x3's rhs in
an ordinary context, not rhsCtxt.  Hence the "certainly_inline" stuff.

Annoyingly, we have to approximate SimplUtils.preInlineUnconditionally.
If we say "yes" when preInlineUnconditionally says "no" the simplifier iterates
indefinitely:
        x = f y
        k = Just x
inline ==>
        k = Just (f y)
float ==>
        x1 = f y
        k = Just x1

This is worse than the slow cascade, so we only want to say "certainly_inline"
if it really is certain.  Look at the note with preInlineUnconditionally
for the various clauses.


************************************************************************
*                                                                      *
                Expressions
*                                                                      *
************************************************************************
-}

occAnal :: OccEnv
        -> CoreExpr
        -> (UsageDetails,       -- Gives info only about the "interesting" Ids
            CoreExpr)

occAnal _   expr@(Type _) = (emptyDetails,         expr)
occAnal _   expr@(Lit _)  = (emptyDetails,         expr)
occAnal env expr@(Var _)  = occAnalApp env (expr, [], [])
    -- At one stage, I gathered the idRuleVars for the variable here too,
    -- which in a way is the right thing to do.
    -- But that went wrong right after specialisation, when
    -- the *occurrences* of the overloaded function didn't have any
    -- rules in them, so the *specialised* versions looked as if they
    -- weren't used at all.

occAnal _ (Coercion co)
  = (addManyOccsSet emptyDetails (coVarsOfCo co), Coercion co)
        -- See Note [Gather occurrences of coercion variables]

{-
Note [Gather occurrences of coercion variables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We need to gather info about what coercion variables appear, so that
we can sort them into the right place when doing dependency analysis.
-}

occAnal env (Tick tickish body)
  | tickish `tickishScopesLike` SoftScope
  = (markAllNonTailCalled usage, Tick tickish body')

  | Breakpoint _ ids <- tickish
  = (usage_lam +++ foldr addManyOccs emptyDetails ids, Tick tickish body')
    -- never substitute for any of the Ids in a Breakpoint

  | otherwise
  = (usage_lam, Tick tickish body')
  where
    !(usage,body') = occAnal env body
    -- for a non-soft tick scope, we can inline lambdas only
    usage_lam = markAllNonTailCalled (markAllInsideLam usage)
                  -- TODO There may be ways to make ticks and join points play
                  -- nicer together, but right now there are problems:
                  --   let j x = ... in tick<t> (j 1)
                  -- Making j a join point may cause the simplifier to drop t
                  -- (if the tick is put into the continuation). So we don't
                  -- count j 1 as a tail call.

occAnal env (Cast expr co)
  = case occAnal env expr of { (usage, expr') ->
    let usage1 = zapDetailsIf (isRhsEnv env) usage
        usage2 = addManyOccsSet usage1 (coVarsOfCo co)
          -- See Note [Gather occurrences of coercion variables]
    in (markAllNonTailCalled usage2, Cast expr' co)
        -- If we see let x = y `cast` co
        -- then mark y as 'Many' so that we don't
        -- immediately inline y again.
    }

occAnal env app@(App _ _)
  = occAnalApp env (collectArgsTicks tickishFloatable app)

-- Ignore type variables altogether
--   (a) occurrences inside type lambdas only not marked as InsideLam
--   (b) type variables not in environment

occAnal env (Lam x body) | isTyVar x
  = case occAnal env body of { (body_usage, body') ->
    (markAllNonTailCalled body_usage, Lam x body')
    }

-- For value lambdas we do a special hack.  Consider
--      (\x. \y. ...x...)
-- If we did nothing, x is used inside the \y, so would be marked
-- as dangerous to dup.  But in the common case where the abstraction
-- is applied to two arguments this is over-pessimistic.
-- So instead, we just mark each binder with its occurrence
-- info in the *body* of the multiple lambda.
-- Then, the simplifier is careful when partially applying lambdas.

occAnal env expr@(Lam _ _)
  = case occAnalLam env binders body of { (usage, tagged_binders, body') ->
    let
        expr'       = mkLams tagged_binders body'
        final_usage = adjustRhsUsage Nothing NonRecursive expr' usage
    in
    (final_usage, expr') }
  where
    (binders, body)      = collectBinders expr

occAnal env (Case scrut bndr ty alts)
  = case occ_anal_scrut scrut alts     of { (scrut_usage, scrut') ->
    case mapAndUnzip occ_anal_alt alts of { (alts_usage_s, alts')   ->
    let
        alts_usage  = foldr combineAltsUsageDetails emptyDetails alts_usage_s
        (alts_usage1, tagged_bndr) = tag_case_bndr alts_usage bndr
        total_usage = markAllNonTailCalled scrut_usage +++ alts_usage1
                        -- Alts can have tail calls, but the scrutinee can't
    in
    total_usage `seq` (total_usage, Case scrut' tagged_bndr ty alts') }}
  where
        -- Note [Case binder usage]
        -- ~~~~~~~~~~~~~~~~~~~~~~~~
        -- The case binder gets a usage of either "many" or "dead", never "one".
        -- Reason: we like to inline single occurrences, to eliminate a binding,
        -- but inlining a case binder *doesn't* eliminate a binding.
        -- We *don't* want to transform
        --      case x of w { (p,q) -> f w }
        -- into
        --      case x of w { (p,q) -> f (p,q) }
    tag_case_bndr usage bndr
      = (usage', setIdOccInfo bndr final_occ_info)
      where
        occ_info       = lookupDetails usage bndr
        usage'         = usage `delDetails` bndr
        final_occ_info = case occ_info of IAmDead -> IAmDead
                                          _       -> noOccInfo

    alt_env = mkAltEnv env scrut bndr
    occ_anal_alt = occAnalAlt alt_env

    occ_anal_scrut (Var v) (alt1 : other_alts)
        | not (null other_alts) || not (isDefaultAlt alt1)
        = (mkOneOcc env v True 0, Var v)
            -- The 'True' says that the variable occurs in an interesting
            -- context; the case has at least one non-default alternative
    occ_anal_scrut (Tick t e) alts
        | t `tickishScopesLike` SoftScope
          -- No reason to not look through all ticks here, but only
          -- for soft-scoped ticks we can do so without having to
          -- update returned occurance info (see occAnal)
        = second (Tick t) $ occ_anal_scrut e alts

    occ_anal_scrut scrut _alts
        = occAnal (vanillaCtxt env) scrut    -- No need for rhsCtxt

occAnal env (Let bind body)
  = case occAnal env body                of { (body_usage, body') ->
    case occAnalBind env NotTopLevel
                     noImpRuleEdges bind
                     body_usage          of { (final_usage, new_binds) ->
       (final_usage, mkLets new_binds body') }}

occAnalArgs :: OccEnv -> [CoreExpr] -> [OneShots] -> (UsageDetails, [CoreExpr])
occAnalArgs _ [] _
  = (emptyDetails, [])

occAnalArgs env (arg:args) one_shots
  | isTypeArg arg
  = case occAnalArgs env args one_shots of { (uds, args') ->
    (uds, arg:args') }

  | otherwise
  = case argCtxt env one_shots           of { (arg_env, one_shots') ->
    case occAnal arg_env arg             of { (uds1, arg') ->
    case occAnalArgs env args one_shots' of { (uds2, args') ->
    (uds1 +++ uds2, arg':args') }}}

{-
Applications are dealt with specially because we want
the "build hack" to work.

Note [Arguments of let-bound constructors]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
    f x = let y = expensive x in
          let z = (True,y) in
          (case z of {(p,q)->q}, case z of {(p,q)->q})
We feel free to duplicate the WHNF (True,y), but that means
that y may be duplicated thereby.

If we aren't careful we duplicate the (expensive x) call!
Constructors are rather like lambdas in this way.
-}

occAnalApp :: OccEnv
           -> (Expr CoreBndr, [Arg CoreBndr], [Tickish Id])
           -> (UsageDetails, Expr CoreBndr)
occAnalApp env (Var fun, args, ticks)
  | null ticks = (uds, mkApps (Var fun) args')
  | otherwise  = (uds, mkTicks ticks $ mkApps (Var fun) args')
  where
    uds = fun_uds +++ final_args_uds

    !(args_uds, args') = occAnalArgs env args one_shots
    !final_args_uds
       | isRhsEnv env && is_exp = markAllNonTailCalled $
                                  markAllInsideLam args_uds
       | otherwise              = markAllNonTailCalled args_uds
       -- We mark the free vars of the argument of a constructor or PAP
       -- as "inside-lambda", if it is the RHS of a let(rec).
       -- This means that nothing gets inlined into a constructor or PAP
       -- argument position, which is what we want.  Typically those
       -- constructor arguments are just variables, or trivial expressions.
       -- We use inside-lam because it's like eta-expanding the PAP.
       --
       -- This is the *whole point* of the isRhsEnv predicate
       -- See Note [Arguments of let-bound constructors]

    n_val_args = valArgCount args
    n_args     = length args
    fun_uds    = mkOneOcc env fun (n_val_args > 0) n_args
    is_exp     = isExpandableApp fun n_val_args
           -- See Note [CONLIKE pragma] in BasicTypes
           -- The definition of is_exp should match that in
           -- Simplify.prepareRhs

    one_shots  = argsOneShots (idStrictness fun) n_val_args
                 -- See Note [Use one-shot info]

occAnalApp env (fun, args, ticks)
  = (markAllNonTailCalled (fun_uds +++ args_uds),
     mkTicks ticks $ mkApps fun' args')
  where
    !(fun_uds, fun') = occAnal (addAppCtxt env args) fun
        -- The addAppCtxt is a bit cunning.  One iteration of the simplifier
        -- often leaves behind beta redexs like
        --      (\x y -> e) a1 a2
        -- Here we would like to mark x,y as one-shot, and treat the whole
        -- thing much like a let.  We do this by pushing some True items
        -- onto the context stack.
    !(args_uds, args') = occAnalArgs env args []

zapDetailsIf :: Bool              -- If this is true
             -> UsageDetails      -- Then do zapDetails on this
             -> UsageDetails
zapDetailsIf True  uds = zapDetails uds
zapDetailsIf False uds = uds

{-
Note [Use one-shot information]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The occurrrence analyser propagates one-shot-lambda information in two
situations:

  * Applications:  eg   build (\c n -> blah)

    Propagate one-shot info from the strictness signature of 'build' to
    the \c n.

    This strictness signature can come from a module interface, in the case of
    an imported function, or from a previous run of the demand analyser.

  * Let-bindings:  eg   let f = \c. let ... in \n -> blah
                        in (build f, build f)

    Propagate one-shot info from the demanand-info on 'f' to the
    lambdas in its RHS (which may not be syntactically at the top)

    This information must have come from a previous run of the demanand
    analyser.

Previously, the demand analyser would *also* set the one-shot information, but
that code was buggy (see #11770), so doing it only in on place, namely here, is
saner.

Note [Binders in case alternatives]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
    case x of y { (a,b) -> f y }
We treat 'a', 'b' as dead, because they don't physically occur in the
case alternative.  (Indeed, a variable is dead iff it doesn't occur in
its scope in the output of OccAnal.)  It really helps to know when
binders are unused.  See esp the call to isDeadBinder in
Simplify.mkDupableAlt

In this example, though, the Simplifier will bring 'a' and 'b' back to
life, beause it binds 'y' to (a,b) (imagine got inlined and
scrutinised y).
-}

occAnalLam :: OccEnv -> [CoreBndr] -> CoreExpr
           -> (UsageDetails, [CoreBndr], CoreExpr)
occAnalLam env [] body
  = case occAnal env body of (body_usage, body') -> (body_usage, [], body')
      -- RHS of thunk or nullary join point
occAnalLam env binders body
  = case occAnal env_body body of { (body_usage, body') ->
    let
        (final_usage, tagged_binders) = tagLamBinders body_usage binders'
                      -- Use binders' to put one-shot info on the lambdas
    in
    (final_usage, tagged_binders, body') }
  where
    (env_body, binders') = oneShotGroup env binders

occAnalAlt :: (OccEnv, Maybe (Id, CoreExpr))
           -> CoreAlt
           -> (UsageDetails, Alt IdWithOccInfo)
occAnalAlt (env, scrut_bind) (con, bndrs, rhs)
  = case occAnal env rhs of { (rhs_usage1, rhs1) ->
    let
        (alt_usg, tagged_bndrs) = tagLamBinders rhs_usage1 bndrs
                                  -- See Note [Binders in case alternatives]
        (alt_usg', rhs2) =
          wrapAltRHS env scrut_bind alt_usg tagged_bndrs rhs1
    in
    (alt_usg', (con, tagged_bndrs, rhs2)) }

wrapAltRHS :: OccEnv
           -> Maybe (Id, CoreExpr)      -- proxy mapping generated by mkAltEnv
           -> UsageDetails              -- usage for entire alt (p -> rhs)
           -> [Var]                     -- alt binders
           -> CoreExpr                  -- alt RHS
           -> (UsageDetails, CoreExpr)
wrapAltRHS env (Just (scrut_var, let_rhs)) alt_usg bndrs alt_rhs
  | occ_binder_swap env
  , scrut_var `usedIn` alt_usg -- bndrs are not be present in alt_usg so this
                               -- handles condition (a) in Note [Binder swap]
  , not captured               -- See condition (b) in Note [Binder swap]
  = ( alt_usg' +++ let_rhs_usg
    , Let (NonRec tagged_scrut_var let_rhs') alt_rhs )
  where
    captured = any (`usedIn` let_rhs_usg) bndrs
    -- The rhs of the let may include coercion variables
    -- if the scrutinee was a cast, so we must gather their
    -- usage. See Note [Gather occurrences of coercion variables]
    (let_rhs_usg, let_rhs') = occAnal env let_rhs
    (alt_usg', tagged_scrut_var) = tagBinder False alt_usg scrut_var

wrapAltRHS _ _ alt_usg _ alt_rhs
  = (alt_usg, alt_rhs)

{-
************************************************************************
*                                                                      *
                    OccEnv
*                                                                      *
************************************************************************
-}

data OccEnv
  = OccEnv { occ_encl       :: !OccEncl      -- Enclosing context information
           , occ_one_shots  :: !OneShots     -- Tells about linearity
           , occ_gbl_scrut  :: GlobalScruts
           , occ_rule_act   :: Activation -> Bool   -- Which rules are active
             -- See Note [Finding rule RHS free vars]
           , occ_binder_swap :: !Bool -- enable the binder_swap
             -- See CorePrep Note [Dead code in CorePrep]
    }

type GlobalScruts = IdSet   -- See Note [Binder swap on GlobalId scrutinees]

-----------------------------
-- OccEncl is used to control whether to inline into constructor arguments
-- For example:
--      x = (p,q)               -- Don't inline p or q
--      y = /\a -> (p a, q a)   -- Still don't inline p or q
--      z = f (p,q)             -- Do inline p,q; it may make a rule fire
-- So OccEncl tells enought about the context to know what to do when
-- we encounter a constructor application or PAP.

data OccEncl
  = OccRhs              -- RHS of let(rec), albeit perhaps inside a type lambda
                        -- Don't inline into constructor args here
  | OccVanilla          -- Argument of function, body of lambda, scruintee of case etc.
                        -- Do inline into constructor args here

instance Outputable OccEncl where
  ppr OccRhs     = text "occRhs"
  ppr OccVanilla = text "occVanilla"

type OneShots = [OneShotInfo]
        -- []           No info
        --
        -- one_shot_info:ctxt    Analysing a function-valued expression that
        --                       will be applied as described by one_shot_info

initOccEnv :: (Activation -> Bool) -> OccEnv
initOccEnv active_rule
  = OccEnv { occ_encl      = OccVanilla
           , occ_one_shots = []
           , occ_gbl_scrut = emptyVarSet
           , occ_rule_act  = active_rule
           , occ_binder_swap = True }

vanillaCtxt :: OccEnv -> OccEnv
vanillaCtxt env = env { occ_encl = OccVanilla, occ_one_shots = [] }

rhsCtxt :: OccEnv -> OccEnv
rhsCtxt env = env { occ_encl = OccRhs, occ_one_shots = [] }

argCtxt :: OccEnv -> [OneShots] -> (OccEnv, [OneShots])
argCtxt env []
  = (env { occ_encl = OccVanilla, occ_one_shots = [] }, [])
argCtxt env (one_shots:one_shots_s)
  = (env { occ_encl = OccVanilla, occ_one_shots = one_shots }, one_shots_s)

isRhsEnv :: OccEnv -> Bool
isRhsEnv (OccEnv { occ_encl = OccRhs })     = True
isRhsEnv (OccEnv { occ_encl = OccVanilla }) = False

oneShotGroup :: OccEnv -> [CoreBndr]
             -> ( OccEnv
                , [CoreBndr] )
        -- The result binders have one-shot-ness set that they might not have had originally.
        -- This happens in (build (\c n -> e)).  Here the occurrence analyser
        -- linearity context knows that c,n are one-shot, and it records that fact in
        -- the binder. This is useful to guide subsequent float-in/float-out tranformations

oneShotGroup env@(OccEnv { occ_one_shots = ctxt }) bndrs
  = go ctxt bndrs []
  where
    go ctxt [] rev_bndrs
      = ( env { occ_one_shots = ctxt, occ_encl = OccVanilla }
        , reverse rev_bndrs )

    go [] bndrs rev_bndrs
      = ( env { occ_one_shots = [], occ_encl = OccVanilla }
        , reverse rev_bndrs ++ bndrs )

    go ctxt (bndr:bndrs) rev_bndrs
      | isId bndr

      = case ctxt of
          []                -> go []   bndrs (bndr : rev_bndrs)
          (one_shot : ctxt) -> go ctxt bndrs (bndr': rev_bndrs)
            where
               bndr' = updOneShotInfo bndr one_shot
               -- Use updOneShotInfo, not setOneShotInfo, as pre-existing
               -- one-shot info might be better than what we can infer, e.g.
               -- due to explicit use of the magic 'oneShot' function.
               -- See Note [The oneShot function]

       | otherwise
      = go ctxt bndrs (bndr:rev_bndrs)

addAppCtxt :: OccEnv -> [Arg CoreBndr] -> OccEnv
addAppCtxt env@(OccEnv { occ_one_shots = ctxt }) args
  = env { occ_one_shots = replicate (valArgCount args) OneShotLam ++ ctxt }

transClosureFV :: UniqFM VarSet -> UniqFM VarSet
-- If (f,g), (g,h) are in the input, then (f,h) is in the output
--                                   as well as (f,g), (g,h)
transClosureFV env
  | no_change = env
  | otherwise = transClosureFV (listToUFM new_fv_list)
  where
    (no_change, new_fv_list) = mapAccumL bump True (nonDetUFMToList env)
      -- It's OK to use nonDetUFMToList here because we'll forget the
      -- ordering by creating a new set with listToUFM
    bump no_change (b,fvs)
      | no_change_here = (no_change, (b,fvs))
      | otherwise      = (False,     (b,new_fvs))
      where
        (new_fvs, no_change_here) = extendFvs env fvs

-------------
extendFvs_ :: UniqFM VarSet -> VarSet -> VarSet
extendFvs_ env s = fst (extendFvs env s)   -- Discard the Bool flag

extendFvs :: UniqFM VarSet -> VarSet -> (VarSet, Bool)
-- (extendFVs env s) returns
--     (s `union` env(s), env(s) `subset` s)
extendFvs env s
  | isNullUFM env
  = (s, True)
  | otherwise
  = (s `unionVarSet` extras, extras `subVarSet` s)
  where
    extras :: VarSet    -- env(s)
    extras = nonDetFoldUFM unionVarSet emptyVarSet $
      -- It's OK to use nonDetFoldUFM here because unionVarSet commutes
             intersectUFM_C (\x _ -> x) env s

{-
************************************************************************
*                                                                      *
                    Binder swap
*                                                                      *
************************************************************************

Note [Binder swap]
~~~~~~~~~~~~~~~~~~
We do these two transformations right here:

 (1)   case x of b { pi -> ri }
    ==>
      case x of b { pi -> let x=b in ri }

 (2)  case (x |> co) of b { pi -> ri }
    ==>
      case (x |> co) of b { pi -> let x = b |> sym co in ri }

    Why (2)?  See Note [Case of cast]

In both cases, in a particular alternative (pi -> ri), we only
add the binding if
  (a) x occurs free in (pi -> ri)
        (ie it occurs in ri, but is not bound in pi)
  (b) the pi does not bind b (or the free vars of co)
We need (a) and (b) for the inserted binding to be correct.

For the alternatives where we inject the binding, we can transfer
all x's OccInfo to b.  And that is the point.

Notice that
  * The deliberate shadowing of 'x'.
  * That (a) rapidly becomes false, so no bindings are injected.

The reason for doing these transformations here is because it allows
us to adjust the OccInfo for 'x' and 'b' as we go.

  * Suppose the only occurrences of 'x' are the scrutinee and in the
    ri; then this transformation makes it occur just once, and hence
    get inlined right away.

  * If we do this in the Simplifier, we don't know whether 'x' is used
    in ri, so we are forced to pessimistically zap b's OccInfo even
    though it is typically dead (ie neither it nor x appear in the
    ri).  There's nothing actually wrong with zapping it, except that
    it's kind of nice to know which variables are dead.  My nose
    tells me to keep this information as robustly as possible.

The Maybe (Id,CoreExpr) passed to occAnalAlt is the extra let-binding
{x=b}; it's Nothing if the binder-swap doesn't happen.

There is a danger though.  Consider
      let v = x +# y
      in case (f v) of w -> ...v...v...
And suppose that (f v) expands to just v.  Then we'd like to
use 'w' instead of 'v' in the alternative.  But it may be too
late; we may have substituted the (cheap) x+#y for v in the
same simplifier pass that reduced (f v) to v.

I think this is just too bad.  CSE will recover some of it.

Note [Case of cast]
~~~~~~~~~~~~~~~~~~~
Consider        case (x `cast` co) of b { I# ->
                ... (case (x `cast` co) of {...}) ...
We'd like to eliminate the inner case.  That is the motivation for
equation (2) in Note [Binder swap].  When we get to the inner case, we
inline x, cancel the casts, and away we go.

Note [Binder swap on GlobalId scrutinees]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When the scrutinee is a GlobalId we must take care in two ways

 i) In order to *know* whether 'x' occurs free in the RHS, we need its
    occurrence info. BUT, we don't gather occurrence info for
    GlobalIds.  That's the reason for the (small) occ_gbl_scrut env in
    OccEnv is for: it says "gather occurrence info for these".

 ii) We must call localiseId on 'x' first, in case it's a GlobalId, or
     has an External Name. See, for example, SimplEnv Note [Global Ids in
     the substitution].

Note [Zap case binders in proxy bindings]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
From the original
     case x of cb(dead) { p -> ...x... }
we will get
     case x of cb(live) { p -> let x = cb in ...x... }

Core Lint never expects to find an *occurrence* of an Id marked
as Dead, so we must zap the OccInfo on cb before making the
binding x = cb.  See Trac #5028.

Historical note [no-case-of-case]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We *used* to suppress the binder-swap in case expressions when
-fno-case-of-case is on.  Old remarks:
    "This happens in the first simplifier pass,
    and enhances full laziness.  Here's the bad case:
            f = \ y -> ...(case x of I# v -> ...(case x of ...) ... )
    If we eliminate the inner case, we trap it inside the I# v -> arm,
    which might prevent some full laziness happening.  I've seen this
    in action in spectral/cichelli/Prog.hs:
             [(m,n) | m <- [1..max], n <- [1..max]]
    Hence the check for NoCaseOfCase."
However, now the full-laziness pass itself reverses the binder-swap, so this
check is no longer necessary.

Historical note [Suppressing the case binder-swap]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This old note describes a problem that is also fixed by doing the
binder-swap in OccAnal:

    There is another situation when it might make sense to suppress the
    case-expression binde-swap. If we have

        case x of w1 { DEFAULT -> case x of w2 { A -> e1; B -> e2 }
                       ...other cases .... }

    We'll perform the binder-swap for the outer case, giving

        case x of w1 { DEFAULT -> case w1 of w2 { A -> e1; B -> e2 }
                       ...other cases .... }

    But there is no point in doing it for the inner case, because w1 can't
    be inlined anyway.  Furthermore, doing the case-swapping involves
    zapping w2's occurrence info (see paragraphs that follow), and that
    forces us to bind w2 when doing case merging.  So we get

        case x of w1 { A -> let w2 = w1 in e1
                       B -> let w2 = w1 in e2
                       ...other cases .... }

    This is plain silly in the common case where w2 is dead.

    Even so, I can't see a good way to implement this idea.  I tried
    not doing the binder-swap if the scrutinee was already evaluated
    but that failed big-time:

            data T = MkT !Int

            case v of w  { MkT x ->
            case x of x1 { I# y1 ->
            case x of x2 { I# y2 -> ...

    Notice that because MkT is strict, x is marked "evaluated".  But to
    eliminate the last case, we must either make sure that x (as well as
    x1) has unfolding MkT y1.  The straightforward thing to do is to do
    the binder-swap.  So this whole note is a no-op.

It's fixed by doing the binder-swap in OccAnal because we can do the
binder-swap unconditionally and still get occurrence analysis
information right.
-}

mkAltEnv :: OccEnv -> CoreExpr -> Id -> (OccEnv, Maybe (Id, CoreExpr))
-- Does two things: a) makes the occ_one_shots = OccVanilla
--                  b) extends the GlobalScruts if possible
--                  c) returns a proxy mapping, binding the scrutinee
--                     to the case binder, if possible
mkAltEnv env@(OccEnv { occ_gbl_scrut = pe }) scrut case_bndr
  = case stripTicksTopE (const True) scrut of
      Var v           -> add_scrut v case_bndr'
      Cast (Var v) co -> add_scrut v (Cast case_bndr' (mkSymCo co))
                          -- See Note [Case of cast]
      _               -> (env { occ_encl = OccVanilla }, Nothing)

  where
    add_scrut v rhs = ( env { occ_encl = OccVanilla, occ_gbl_scrut = pe `extendVarSet` v }
                      , Just (localise v, rhs) )

    case_bndr' = Var (zapIdOccInfo case_bndr) -- See Note [Zap case binders in proxy bindings]
    localise scrut_var = mkLocalIdOrCoVar (localiseName (idName scrut_var)) (idType scrut_var)
        -- Localise the scrut_var before shadowing it; we're making a
        -- new binding for it, and it might have an External Name, or
        -- even be a GlobalId; Note [Binder swap on GlobalId scrutinees]
        -- Also we don't want any INLINE or NOINLINE pragmas!

{-
************************************************************************
*                                                                      *
\subsection[OccurAnal-types]{OccEnv}
*                                                                      *
************************************************************************
-}

type OccInfoEnv = IdEnv OccInfo -- A finite map from ids to their usage
                -- INVARIANT: never IAmDead
                -- (Deadness is signalled by not being in the map at all)

type ZappedSet = OccInfoEnv -- Values are ignored

data UsageDetails
  = UD { ud_env       :: !OccInfoEnv
       , ud_z_many    :: ZappedSet
       , ud_z_in_lam  :: ZappedSet
       , ud_z_no_tail :: ZappedSet }
  -- INVARIANT: All three zapped sets are subsets of the OccInfoEnv

instance Outputable UsageDetails where
  ppr ud = ppr (ud_env (flattenUsageDetails ud))

-------------------
-- UsageDetails API

(+++)          :: UsageDetails -> UsageDetails -> UsageDetails
combineAltsUsageDetails :: UsageDetails -> UsageDetails -> UsageDetails
mkOneOcc       :: OccEnv -> Id -> InterestingCxt -> JoinArity -> UsageDetails
addOneOcc      :: UsageDetails -> Id -> OccInfo -> UsageDetails
-- Add several occurrences, assumed not to be tail calls
addManyOccs    :: Var -> UsageDetails -> UsageDetails
addManyOccsSet :: UsageDetails -> VarSet -> UsageDetails
delDetails     :: UsageDetails -> Id -> UsageDetails
delDetailsList :: UsageDetails -> [Id] -> UsageDetails
minusDetails   :: UsageDetails -> IdEnv a -> UsageDetails
emptyDetails   :: UsageDetails
isEmptyDetails :: UsageDetails -> Bool
zapDetails     :: UsageDetails -> UsageDetails
markAllMany    :: UsageDetails -> UsageDetails
markAllInsideLam     :: UsageDetails -> UsageDetails
markAllNonTailCalled :: UsageDetails -> UsageDetails
lookupDetails  :: UsageDetails -> Id -> OccInfo
usedIn         :: Id -> UsageDetails -> Bool
udFreeVars     :: VarSet -> UsageDetails -> VarSet

-------------------
(+++) = combineUsageDetailsWith addOccInfo
combineAltsUsageDetails = combineUsageDetailsWith orOccInfo

mkOneOcc env id int_cxt arity
  | isLocalId id
  = singleton $ OneOcc { occ_in_lam  = False
                       , occ_one_br  = True
                       , occ_int_cxt = int_cxt
                       , occ_tail    = AlwaysTailCalled arity }
  | id `elemVarEnv` occ_gbl_scrut env
  = singleton noOccInfo

  | otherwise
  = emptyDetails
  where
    singleton info = emptyDetails { ud_env = unitVarEnv id info }

addOneOcc ud id info
  = ud { ud_env = extendVarEnv_C plus_zapped (ud_env ud) id info }
      `alterZappedSets` (`delVarEnv` id)
  where
    plus_zapped old new = doZapping ud id old `addOccInfo` new

addManyOccsSet usage id_set = nonDetFoldUFM addManyOccs usage id_set
  -- It's OK to use nonDetFoldUFM here because addManyOccs commutes

addManyOccs v u | isId v    = addOneOcc u v noOccInfo
                | otherwise = u
        -- Give a non-committal binder info (i.e noOccInfo) because
        --   a) Many copies of the specialised thing can appear
        --   b) We don't want to substitute a BIG expression inside a RULE
        --      even if that's the only occurrence of the thing
        --      (Same goes for INLINE.)


delDetails ud bndr
  = ud `alterUsageDetails` (`delVarEnv` bndr)

delDetailsList ud bndrs
  = ud `alterUsageDetails` (`delVarEnvList` bndrs)

minusDetails ud bndrs
  = ud `alterUsageDetails` (`minusVarEnv` bndrs)

emptyDetails = UD { ud_env       = emptyVarEnv
                  , ud_z_many    = emptyVarEnv
                  , ud_z_in_lam  = emptyVarEnv
                  , ud_z_no_tail = emptyVarEnv }

isEmptyDetails = isEmptyVarEnv . ud_env

markAllMany          ud = ud { ud_z_many    = ud_env ud }
markAllInsideLam     ud = ud { ud_z_in_lam  = ud_env ud }
markAllNonTailCalled ud = ud { ud_z_no_tail = ud_env ud }

zapDetails = markAllMany . markAllNonTailCalled -- effectively sets to noOccInfo

lookupDetails ud id
  = case lookupVarEnv (ud_env ud) id of
      Just occ -> doZapping ud id occ
      Nothing  -> IAmDead

v `usedIn` ud = isExportedId v || v `elemVarEnv` ud_env ud

-- Find the subset of bndrs that are mentioned in uds
udFreeVars bndrs ud = intersectUFM_C (\b _ -> b) bndrs (ud_env ud)

-------------------
-- Auxiliary functions for UsageDetails implementation

combineUsageDetailsWith :: (OccInfo -> OccInfo -> OccInfo)
                        -> UsageDetails -> UsageDetails -> UsageDetails
combineUsageDetailsWith plus_occ_info ud1 ud2
  = UD { ud_env       = plusVarEnv_C plus_occ_info (ud_env ud1) (ud_env ud2)
       , ud_z_many    = plusVarEnv (ud_z_many    ud1) (ud_z_many    ud2)
       , ud_z_in_lam  = plusVarEnv (ud_z_in_lam  ud1) (ud_z_in_lam  ud2)
       , ud_z_no_tail = plusVarEnv (ud_z_no_tail ud1) (ud_z_no_tail ud2) }

doZapping :: UsageDetails -> Var -> OccInfo -> OccInfo
doZapping ud var occ
  = doZappingByUnique ud (varUnique var) occ

doZappingByUnique :: UsageDetails -> Unique -> OccInfo -> OccInfo
doZappingByUnique ud uniq
  = (if | in_subset ud_z_many    -> markMany
        | in_subset ud_z_in_lam  -> markInsideLam
        | otherwise              -> id) .
    (if | in_subset ud_z_no_tail -> markNonTailCalled
        | otherwise              -> id)
  where
    in_subset field = uniq `elemVarEnvByKey` field ud

alterZappedSets :: UsageDetails -> (ZappedSet -> ZappedSet) -> UsageDetails
alterZappedSets ud f
  = ud { ud_z_many    = f (ud_z_many    ud)
       , ud_z_in_lam  = f (ud_z_in_lam  ud)
       , ud_z_no_tail = f (ud_z_no_tail ud) }

alterUsageDetails :: UsageDetails -> (OccInfoEnv -> OccInfoEnv) -> UsageDetails
alterUsageDetails ud f
  = ud { ud_env = f (ud_env ud) }
      `alterZappedSets` f

flattenUsageDetails :: UsageDetails -> UsageDetails
flattenUsageDetails ud
  = ud { ud_env = mapUFM_Directly (doZappingByUnique ud) (ud_env ud) }
      `alterZappedSets` const emptyVarEnv

-------------------
-- | Apply adjustments from join-point-hood and one-shot-ness to usage details
-- from a lambda expression or a binding's RHS. Can't be done from occAnalRhs
-- because it doesn't yet know whether the binding will become a join point.
--
-- Tail calls can happen indirectly from join points (since they're necessarily
-- invoked by tail calls) but not from regular functions. Thus if the binder
-- isn't a join id (and we're not making it one), we drop all tail-call info
-- from its RHS. Also drop tail calls if the join point is under- or
-- oversaturated (since then its body isn't truly in tail position).
--
-- If a function or join point is non-one-shot, its free variables get marked as
-- occurring inside a lambda. A lambda group is one-shot if each of its value
-- lambdas is one-shot. A free-standing function is one-shot if its lambda group
-- is one-shot. A binding is one-shot if either
--
--   1. It's for a thunk, or
--   2. It's for a function and its outer lambda group is one-shot, or
--   3. It's for a non-recursive join point of join arity n, and after its
--      initial n lambdas, its outer lambda group is one-shot. (Most join points
--      don't have such extra lambdas, so they're one-shot iff non-recursive.)
adjustRhsUsage :: Maybe JoinArity -> RecFlag
               -> CoreExpr -- RHS or expression (with lambdas), AFTER occ anal
               -> UsageDetails -> UsageDetails
adjustRhsUsage mb_join_arity rec_flag expr usage
  = maybe_mark_lam (maybe_drop_tails usage)
  where
    (bndrs, _) = collectBinders expr

    maybe_mark_lam ud   | one_shot   = ud
                        | otherwise  = markAllInsideLam ud
    maybe_drop_tails ud | exact_join = ud
                        | otherwise  = markAllNonTailCalled ud

    one_shot = case mb_join_arity of
                 Just join_arity
                   | isRec rec_flag -> False
                   | otherwise      -> all_one_shot (drop join_arity bndrs)
                 Nothing            -> all_one_shot bndrs

    all_one_shot = all (\bndr -> not (isId bndr) || isOneShotBndr bndr)

    exact_join = case mb_join_arity of
                   Just join_arity -> join_arity == length bndrs
                   _               -> False

type IdWithOccInfo = Id

tagLamBinders :: UsageDetails          -- Of scope
              -> [Id]                  -- Binders
              -> (UsageDetails,        -- Details with binders removed
                 [IdWithOccInfo])    -- Tagged binders
-- Used for lambda and case binders
-- It copes with the fact that lambda bindings can have a
-- stable unfolding, used for join points
tagLamBinders usage binders = usage' `seq` (usage', bndrs')
  where
    (usage', bndrs') = mapAccumR tag_lam usage binders
    tag_lam usage bndr = (usage2, bndr')
      where
        (usage1, bndr') = tagBinder False usage bndr
        usage2 | isId bndr = addManyOccsSet usage1 (idUnfoldingVars bndr)
                               -- This is effectively the RHS of a
                               -- non-join-point binding, so it's okay to use
                               -- addManyOccsSet, which assumes no tail calls
               | otherwise = usage1

tagBinder :: Bool                   -- Can it be a join point?
          -> UsageDetails           -- Of scope
          -> CoreBndr               -- Binders
          -> (UsageDetails,         -- Details with binders removed
              IdWithOccInfo)        -- Tagged binders

tagBinder make_join usage binder
 = let
     usage'  = usage `delDetails` binder
     binder' | make_join = setBinderOcc usage binder
             | otherwise = setBinderOcc (markAllNonTailCalled usage) binder
   in
   usage' `seq` (usage', binder')

setBinderOcc :: UsageDetails -> CoreBndr -> CoreBndr
setBinderOcc usage bndr
  | isTyVar bndr      = bndr
  | isExportedId bndr = if isNoOcc (idOccInfo bndr)
                          then bndr
                          else setIdOccInfo bndr noOccInfo
            -- Don't use local usage info for visible-elsewhere things
            -- BUT *do* erase any IAmALoopBreaker annotation, because we're
            -- about to re-generate it and it shouldn't be "sticky"

  | otherwise = setIdOccInfo bndr occ_info
  where
    occ_info = lookupDetails usage bndr

-- | Decide whether some bindings should be made into join points or not.
-- Returns `False` if *either* they can't be join points *or* they already
-- are. Note that it's an all-or-nothing decision, as if multiple binders are
-- given, they're assumed to be mutually recursive.
--
-- See Note [Invariants for join points] in IdInfo.
canBecomeJoinPoints :: TopLevelFlag -> RecFlag -> UsageDetails
                    -> [(CoreBndr, CoreExpr)]
                    -> Bool
canBecomeJoinPoints TopLevel _ _ _
  = False
canBecomeJoinPoints NotTopLevel rec_flag usage pairs
  = all ok pairs
  where
    ok (bndr, rhs)
      | isJoinId bndr
      = False -- Already a join id (won't be in analysis anyway)
      | AlwaysTailCalled arity <- tailCallInfo (lookupDetails usage bndr)
      , not (isRec rec_flag && arity /= lambda_count rhs)
          -- Recursive join points can't be partially applied
      , isValidJoinPointType arity (idType bndr)
      = True
      | otherwise
      = False

    lambda_count expr = length bndrs where (bndrs, _) = collectBinders expr

willBeJoinId_maybe :: CoreBndr -> Maybe JoinArity
willBeJoinId_maybe bndr
  | AlwaysTailCalled arity <- tailCallInfo (idOccInfo bndr)
  = Just arity
  | otherwise
  = isJoinId_maybe bndr

{-
************************************************************************
*                                                                      *
\subsection{Operations over OccInfo}
*                                                                      *
************************************************************************
-}

markMany, markInsideLam, markNonTailCalled :: OccInfo -> OccInfo

markMany IAmDead = IAmDead
markMany occ     = ManyOccs { occ_tail = occ_tail occ }

markInsideLam occ@(OneOcc {}) = occ { occ_in_lam = True }
markInsideLam occ             = occ

markNonTailCalled IAmDead = IAmDead
markNonTailCalled occ     = occ { occ_tail = NoTailCallInfo }

addOccInfo, orOccInfo :: OccInfo -> OccInfo -> OccInfo

addOccInfo a1 a2  = ASSERT( not (isDeadOcc a1 || isDeadOcc a2) )
                    ManyOccs { occ_tail = tailCallInfo a1 `andTailCallInfo`
                                          tailCallInfo a2 }
                                -- Both branches are at least One
                                -- (Argument is never IAmDead)

-- (orOccInfo orig new) is used
-- when combining occurrence info from branches of a case

orOccInfo (OneOcc { occ_in_lam = in_lam1, occ_int_cxt = int_cxt1
                  , occ_tail   = tail1 })
          (OneOcc { occ_in_lam = in_lam2, occ_int_cxt = int_cxt2
                  , occ_tail   = tail2 })
  = OneOcc { occ_in_lam  = in_lam1 || in_lam2
           , occ_one_br  = False -- False, because it occurs in both branches
           , occ_int_cxt = int_cxt1 && int_cxt2
           , occ_tail    = tail1 `andTailCallInfo` tail2 }
orOccInfo a1 a2 = ASSERT( not (isDeadOcc a1 || isDeadOcc a2) )
                  ManyOccs { occ_tail = tailCallInfo a1 `andTailCallInfo`
                                        tailCallInfo a2 }

andTailCallInfo :: TailCallInfo -> TailCallInfo -> TailCallInfo
andTailCallInfo info@(AlwaysTailCalled arity1) (AlwaysTailCalled arity2)
  | arity1 == arity2 = info
andTailCallInfo _ _  = NoTailCallInfo
