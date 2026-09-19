%---------------------------------------------------------------------------------------------------------
%
%  Transform FOL Axioms 
% 
%  N. E. Fuchs
%  University of Zurich
%  
%  11 June 2012
%
%---------------------------------------------------------------------------------------------------------
%
%  Change History
%
%  August 20, 2001: added (a modified version) of Uta Schwertel's code to unravel quantifier lists to 
%                   nested standard notation
%
%  August 23, 2001: transform_fol_axioms/1 will now fail if there are no FOL axioms 
%
%---------------------------------------------------------------------------------------------------------
%
%  Technical Details
%
%  transform the external representation of FOL axioms into their internal representation, i.e. add indices 
%  to atoms and unravel quantifier lists
%
%  form of FOL axioms: 'fol_axiom(Index, Formula, Text)' where Index is an integer, Formula is a FOL
%  formula, and Text is a string
%
%  syntax of FOL: negation '-', conjunction '&', disjunction 'v', implication '=>', universal quantification
%  'forall(X, Formula)', existential quantification 'exists(X, Formula)'; in FOL axioms nested universal 
%  quantifiers or nested existential quantifiers can alternatively be written using quantifier lists, e.g. 
%  'forall(X, forall(Y, exists(U, exists(V, Formula))))' as 'forall([X,Y], exists([U,V],Formula))'
%
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
%  declarations
%
%---------------------------------------------------------------------------------------------------------

:- module(transform_fol_axioms, [transform_fol_axioms/2]).

:- use_module(auxiliary_axioms).
:- use_module(support).

:- op(400,  xfx, :).           % label
:- op(400,  fy, -).            % negation
:- op(400,  fy, ~).            % negation as failure
:- op(400,  fy, can).          % possibility 
:- op(400,  fy, must).         % necessity
:- op(400,  fy, may).          % admission 
:- op(400,  fy, should).       % recommendation
:- op(500, xfy, &).            % conjunction
:- op(600, xfy, v).            % disjunction
:- op(650, xfy, =>).           % implication 


%---------------------------------------------------------------------------------------------------------
%
%  for all FOL axioms 'fol_axiom(Index, Formula, Text)'
%
%    replace atomic conditions A in Formula  by A' - fol_axiom(Index) where A' has the additional first
%    argument World
%
%    unravel quantifier lists in Formula to nested standard notation
%
%  conjoin the modified formulas of all FOL axioms into one formula
%
%---------------------------------------------------------------------------------------------------------

transform_fol_axioms(World, FormulaFOLAxioms) :-
  setof(UnravelledIndexedExtendedFormula, transform_formula(World, UnravelledIndexedExtendedFormula), UnravelledIndexedExtendedFormulas),
  conjoin(UnravelledIndexedExtendedFormulas, FormulaFOLAxioms).
  
transform_formula(World, UnravelledIndexedExtendedFormula) :-
  fol_axiom(Index, Formula, _Text), 
  add_world_and_index_to_atoms(World, Formula, Index, IndexedExtendedFormula),
  unravel_quantifier_lists(IndexedExtendedFormula, UnravelledIndexedExtendedFormula).

%---------------------------------------------------------------------------------------------------------
%
%  replace atomic conditions 'A' by 'A - fol_axiom(Index)' and add World argument to A
%  
%---------------------------------------------------------------------------------------------------------

add_world_and_index_to_atoms(World, forall(X, Formula), Index, forall(X, IndexedFormula)) :-
  !,
  add_world_and_index_to_atoms(World, Formula, Index, IndexedFormula).
add_world_and_index_to_atoms(World, exists(X, Formula), Index, exists(X, IndexedFormula)) :-
  !,
  add_world_and_index_to_atoms(World, Formula, Index, IndexedFormula).
add_world_and_index_to_atoms(World, Formula1 & Formula2, Index, IndexedFormula1 & IndexedFormula2) :-
  !,
  add_world_and_index_to_atoms(World, Formula1, Index, IndexedFormula1),
  add_world_and_index_to_atoms(World, Formula2, Index, IndexedFormula2).
add_world_and_index_to_atoms(World, Formula1 v Formula2, Index, IndexedFormula1 v IndexedFormula2) :-
  !,
  add_world_and_index_to_atoms(World, Formula1, Index, IndexedFormula1),
  add_world_and_index_to_atoms(World, Formula2, Index, IndexedFormula2).
add_world_and_index_to_atoms(World, Formula1 => Formula2, Index, IndexedFormula1 => IndexedFormula2) :-
  !,
  add_world_and_index_to_atoms(World, Formula1, Index, IndexedFormula1),
  add_world_and_index_to_atoms(World, Formula2, Index, IndexedFormula2).
add_world_and_index_to_atoms(World, - Formula, Index, - IndexedFormula) :-
  !,
  add_world_and_index_to_atoms(World, Formula, Index, IndexedFormula).
add_world_and_index_to_atoms(World, Formula, Index, (ExtendedFormula - fol_axiom(Index))) :-
  (
    % add World argument unless Formula is a built-in Prolog predicate
    predicate_property(Formula, built_in)
    ->
    ExtendedFormula = Formula
  ;
    Formula =.. [Functor|Arguments],
    ExtendedFormula =.. [Functor|[World|Arguments]]
  ).

%---------------------------------------------------------------------------------------------------------
%
%  unravel quantifier lists to nested standard notation
%
%  keep nested formulas
%
%---------------------------------------------------------------------------------------------------------

unravel_quantifier_lists(forall(X, Formula), forall(X, UnravelledFormula)) :- 
  var(X),
  !,
  unravel_quantifier_lists(Formula, UnravelledFormula). 
unravel_quantifier_lists(forall([], Formula), UnravelledFormula) :-
  !,
  unravel_quantifier_lists(Formula, UnravelledFormula).
unravel_quantifier_lists(forall([X|Xs], Formula), forall(X, UnravelledFormula)) :-
  !,
  unravel_quantifier_lists(forall(Xs, Formula), UnravelledFormula).
unravel_quantifier_lists(exists(X, Formula), exists(X, UnravelledFormula)) :- 
  var(X),
  !,
  unravel_quantifier_lists(Formula, UnravelledFormula). 
unravel_quantifier_lists(exists([], Formula), UnravelledFormula) :-
  !,
  unravel_quantifier_lists(Formula, UnravelledFormula).
unravel_quantifier_lists(exists([X|Xs], Formula), exists(X, UnravelledFormula)) :-
  !,
  unravel_quantifier_lists(exists(Xs, Formula), UnravelledFormula).
unravel_quantifier_lists(Formula1 & Formula2, UnravelledFormula1 & UnravelledFormula2) :-
  !,
  unravel_quantifier_lists(Formula1, UnravelledFormula1),
  unravel_quantifier_lists(Formula2, UnravelledFormula2).
unravel_quantifier_lists(Formula1 v Formula2, UnravelledFormula1 v UnravelledFormula2) :-
  !,
  unravel_quantifier_lists(Formula1, UnravelledFormula1),
  unravel_quantifier_lists(Formula2, UnravelledFormula2). 
unravel_quantifier_lists(Formula1 => Formula2, UnravelledFormula1 => UnravelledFormula2) :-
  !,
  unravel_quantifier_lists(Formula1, UnravelledFormula1),
  unravel_quantifier_lists(Formula2, UnravelledFormula2). 
unravel_quantifier_lists(- Formula, - UnravelledFormula) :-
  !,
  unravel_quantifier_lists(Formula, UnravelledFormula).
unravel_quantifier_lists(Formula, Formula).
  
%---------------------------------------------------------------------------------------------------------
%
%  conjoin list of formulas to one formula 
%  
%---------------------------------------------------------------------------------------------------------

conjoin([Formula], Formula) :-
  !.
conjoin([Formula1, Formula2 | Formulas], Formula1 & RestConjuncts) :-
  conjoin([Formula2 | Formulas], RestConjuncts).

%---------------------------------------------------------------------------------------------------------
