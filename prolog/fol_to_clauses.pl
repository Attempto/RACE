%---------------------------------------------------------------------------------------------------------
%
%  Transform Standard Predicate Logic into Clausal Logic
% 
%  N. E. Fuchs
%  University of Zurich
%
%  8 November 2024
%
%---------------------------------------------------------------------------------------------------------
%
%  Technical Details
%
%  fol_to_clauses(+Formula,-Clauses) converts the first-order Formula into a set of Satchmo Clauses
%
%  based on transform/2 (P. A. Flach, Simply Logical: Intelligent Reasoning by Example, John Wiley & Sons, 
%  1994), and on a modified skolemisation algorithm by Uta Schwertel
%
%  eliminated Flach's transformation to prenex normal form to better handle conjunctions of the form 
%  forall(X, F1) & exists(Y, F2) which otherwise generate a skolem function for the variable Y instead 
%  of a skolem constant
%
%  syntax of Formula: 
%
%    negation '-', disjunction 'v', conjunction '&', implication '=>', universal quantification 
%    'forall(X,Formula)', existential quantification 'exists(X,Formula)', where 'X' is  a Prolog variable
%
%    all atoms of Formula - including true and fail - carry an index, e.g. object(A,customer) - axiom(3), 
%    object(B, card) - theorem(6), or object(C,X) - fol_axiom(7) that shows from which ACE sentence, 
%    respectively auxiliary FOL axiom, the atom was derived, and whether it belongs to the axioms, to 
%    the theorems, or to the auxiliary FOL axioms
%
%  syntax of Satchmo clauses: 
%
%    disjunction ';', conjunction ',', universal quantification is implicit, existential quantification 
%    is handled by skolemisation
%
%    satchmo_clause(Body, Head, Indices) where Body implies Head, and Indices are the sorted indices that 
%    where attached to the atoms of Body and Head when these atoms occurred in Formula (cf. above)
%
%    facts are expressed as satchmo_clause(true, Head, Indices)
%
%    negated clauses are written as satchmo_clause(Body, fail, Indices) 
%
%    Body has the form B1, B2, ..., Bn where Bi have the form Bi1 ; B12 ; ... ; Bin where Bik are logical 
%    atoms without the indices that occurred in Formula
%
%    Head has the form H1 ; H2 ; ... ; Hn where Hi have the form Hi1, Hi2, ..., Him where Hik are logical 
%    atoms without the indices that occurred in Formula 
%
%  checks and modifications:
%
%    copula is marked according to context
%    role of "of"-relation is added
%    clauses that are not range-restricted are deleted
%    quadratic equation is replaced by its two solutions
%
%---------------------------------------------------------------------------------------------------------
%
%  To do
%
%  check clause compaction here and in satchmo/3
%
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
%  declarations
%
%---------------------------------------------------------------------------------------------------------

% module definition and exported predicates
:- module(fol_to_clauses, [fol_to_clauses/2]).

% RACE modules
:- use_module(support).
:- use_module(race_error_logger).

% operators
:- op(400,  xfx, :).           % label
:- op(400,  fy, -).            % negation
:- op(400,  fy, ~).            % negation as failure
:- op(400,  fy, can).          % possibility 
:- op(400,  fy, must).         % necessity
/*
:- op(400,  fy, may).          % admission 
:- op(400,  fy, should).       % recommendation
*/
:- op(500, xfy, &).            % conjunction
:- op(600, xfy, v).            % disjunction
:- op(650, xfy, =>).           % implication 


%---------------------------------------------------------------------------------------------------------
%
%  fol_to_clauses/2
%
%---------------------------------------------------------------------------------------------------------

fol_to_clauses(Formula, Clauses) :-
  rewrite_implications(Formula, FormulaWithoutImplications),
  negations_inside(FormulaWithoutImplications, NegationNormalForm),
  skolemise(NegationNormalForm, SkolemisedNegationNormalForm),
  conjunctive_normal_form(SkolemisedNegationNormalForm, ConjunctiveNormalForm),
  clausal_form(ConjunctiveNormalForm, ConjunctionOfClauses),
  convert_clause_conjunction_into_clause_list(ConjunctionOfClauses, ListOfClauses),
  combine_clauses(ListOfClauses, CombinedClauses),
  modify_clause_set(CombinedClauses, ModifiedClauses),
  remove_underspecification(ModifiedClauses, Clauses). 


%---------------------------------------------------------------------------------------------------------
%
%  rewrite implications
% 
%---------------------------------------------------------------------------------------------------------

rewrite_implications(A => B, -C v D) :-			
  !,
  rewrite_implications(A,C),
  rewrite_implications(B,D).

rewrite_implications(A & B, C & D) :-			
  !,
  rewrite_implications(A,C),					
  rewrite_implications(B,D).

rewrite_implications(A v B, C v D) :-
  !,
  rewrite_implications(A,C),
  rewrite_implications(B,D).

rewrite_implications(-A,-C) :-
  !,
  rewrite_implications(A,C).

rewrite_implications(forall(X,B), forall(X,D)) :-
  !,
  rewrite_implications(B,D).

rewrite_implications(exists(X,B), exists(X,D)) :-
  !,
  rewrite_implications(B,D).

rewrite_implications(A,A) :-						
  literal(A).


%---------------------------------------------------------------------------------------------------------
%
%  move negations inside
%
%  clause set compaction: contrary to the standard transformation to negation normal form do not move 
%  negations into conjunctions and disjunctions of logical atoms
%
%---------------------------------------------------------------------------------------------------------

negations_inside(-(A & B), -ConjunctionInSatchmoNotation) :-				
  % A & B is a conjunction of logical atoms
  conjunction_of_logical_atoms(A & B, ConjunctionInSatchmoNotation, _Index),
  !.

negations_inside(-(A & B), C v D) :-				
  % A & B is not a conjunction of logical atoms
  !,
  negations_inside(-A,C),
  negations_inside(-B,D).

negations_inside(-(A v B), -DisjunctionInSatchmoNotation) :-				
  % A & B is a disjunction of logical atoms
  disjunction_of_logical_atoms(A v B, DisjunctionInSatchmoNotation, _Index),
  !.

negations_inside(-(A v B), C & D) :-				
  % A & B is not a disjunction of logical atoms
  !,
  negations_inside(-A,C),
  negations_inside(-B,D).

negations_inside(-(-A),B) :-						
  !,
  negations_inside(A,B).

negations_inside(-exists(X,A), forall(X,B)) :-	
  !,
  negations_inside(-A,B).

negations_inside(-forall(X,A), exists(X,B)) :-
  !,
  negations_inside(-A,B).

negations_inside(A & B, ConjunctionInSatchmoNotation) :-				
  % A & B is a conjunction of logical atoms
  conjunction_of_logical_atoms(A & B, ConjunctionInSatchmoNotation, _Index),
  !.

negations_inside(A & B, C & D) :-				
  % A & B is not a conjunction of logical atoms
  !,
  negations_inside(A,C),						
  negations_inside(B,D).

negations_inside(A v B, DisjunctionInSatchmoNotation) :-
  % A & B is a disjunction of logical atoms
  disjunction_of_logical_atoms(A v B, DisjunctionInSatchmoNotation, _Index),
  !.

negations_inside(A v B, C v D) :-
  % A & B is not a disjunction of logical atoms
  !,
  negations_inside(A,C),
  negations_inside(B,D).

negations_inside(exists(X,A), exists(X,B)) :-
  !,
  negations_inside(A,B).

negations_inside(forall(X,A), forall(X,B)) :-
  !,
  negations_inside(A,B).

negations_inside(A,A) :-							
  literal(A).


%---------------------------------------------------------------------------------------------------------
%
%  skolemise existentially quantified variables
%
%---------------------------------------------------------------------------------------------------------
/*
:- dynamic(skolem_counter/1).


skolem_counter(1).


skolemise(F1, F2) :-
  % for each run reset skolem_counter to 1
  once(retract(skolem_counter(_))),
  assert(skolem_counter(1)),
  % skolemise with VarList initialised to []
  skolemise(F1, [], F2).
  

skolemise(forall(X, F1), VarList, F2) :-
  !,		
  skolemise(F1, [X|VarList], F2).				

skolemise(exists(X, F1), VarList, F2) :-
  !,
  % get index of the axiom or theorem in which X is skolemised unless X is the World argument
  subterm(SubTerm-Index, F1),
  nonvar(SubTerm),
  SubTerm =.. [_Functor, World, Referent|_Rest], 
  (
    % X is World argument
    World == X
    ->
    % create Skolem term with uninstantiated index
    skolem_term(X, _Index, VarList)
  ;
    % X is Referent argument
    Referent == X
    ->
    % create Skolem term with instantiated index
    skolem_term(X, Index, VarList)
  ),
  % continue						
  skolemise(F1, VarList, F2).

skolemise((F11 & F12), VarList, (F21 & F22)) :-
  !, 
  skolemise(F11, VarList, F21),
  skolemise(F12, VarList, F22).

skolemise((F11 v F12), VarList, (F21 v F22)) :-
  !, 
  skolemise(F11, VarList, F21),
  skolemise(F12, VarList, F22).

skolemise(F, _VarList, F).


skolem_term(X, Index, VarList) :-
  once(retract(skolem_counter(N))),
  N1 is N + 1,
  assert(skolem_counter(N1)),
  name(N, CharList), 								
  name(Functor, [115,107|CharList]),
  copy_term(X, CopiedX),				
  X =.. [Functor|VarList],
  % save the copied variable and Index as global variable named by the main functor of the skolem term for 
  % later use in arithmetic where the variable may be instantiated
  % note 1: b_setval/b_getval – other than assert/retract and nb_setval/nb_getval – preserve the names of variables 
  % note 2: this approach ensures that all occurences of a skolem term get associated with the same variable
  nl, write(skolem_term/3), write(' '), write(b_setval(Functor, (CopiedX, [Index]))), %%%%%%
  b_setval(Functor, (CopiedX, [Index])).
*/


:- dynamic(skolem_counter/1).


skolem_counter(1).


skolemise(F1, F2) :-
  % for each run reset skolem_counter to 1
  once(retract(skolem_counter(_))),
  assert(skolem_counter(1)),
  % skolemise with VarList initialised to []
  skolemise(F1, [], F2).
  
skolemise(forall(X, F1), VarList, F2) :-
  !,		
  skolemise(F1, [X|VarList], F2).				

skolemise(exists(X, F1), VarList, F2) :-
  !,
  skolem_term(X, VarList),						
  skolemise(F1, VarList, F2).

skolemise((F11 & F12), VarList, (F21 & F22)) :-
  !, 
  skolemise(F11, VarList, F21),
  skolemise(F12, VarList, F22).

skolemise((F11 v F12), VarList, (F21 v F22)) :-
  !, 
  skolemise(F11, VarList, F21),
  skolemise(F12, VarList, F22).

skolemise(F, _VarList, F) :-
  % instantiate the index of a skolem term to the index of the clause in which the skolem term occurs the first time
  % indices of clauses in which the skolem term occurs later are ignored with the following effects:
  % A number B is A+1. A is 1. |- A number is 2. -> negative effect: necessary axiom "A is 1." is not listed in the proof results
  % A is 1. B is A+1. A number C is A+2. |- A number is 3. -> positive effect: superfluous axiom "B is A+1." is not listed in the proof results
  % generally it is better not to use bare variables for numerical values
  (
    % get index of the clause in which a skolem term is introduced
    subterm(SubTerm-IndexOfSubterm, F),
    SubTerm =.. [_FunctorSubTerm, _World, Skolem|_RestSubTerm],
    nonvar(Skolem),
    Skolem =.. [FunctorSkolem|_RestSkolem],
    atom_chars(FunctorSkolem, [s,k|_]),
    % check whether index of the skolem term is already instantiated
    b_getval(FunctorSkolem, (CopiedX, [Index])),
    (
      % Index is not yet instantiated
      var(Index)
      ->
      %%%nl, write(skolemise/3), write(' '), write(b_setval(FunctorSkolem, (CopiedX, [IndexOfSubterm]))),
      b_setval(FunctorSkolem, (CopiedX, [IndexOfSubterm]))
    ;
      % Index is already instantiated
      true
    )	
  ;
    % no suitable subterm or Skolem is a variable
    true
  ).			
  

skolem_term(X, VarList) :-
  % objects standing for numbers are represented by skolem terms that need to be associated with their respective numerical 
  % values to be processed in arithmetic expressions; this is achieved by storing the skolem term SK appering in a clause with
  % the index Index as backtrackable global variable (SK, Value,[Index]) where Value is a placeholder for the numerical value
  once(retract(skolem_counter(N))),
  N1 is N + 1,
  assert(skolem_counter(N1)),
  name(N, CharList), 								
  name(Functor, [115,107|CharList]),
  copy_term(X, CopiedX),				
  X =.. [Functor|VarList],
  % save skolem term X and associated (copied) variable CopiedX as global variable named by the main functor of 
  % the skolem term for later use in arithmetic where the variable may be unified with a numerical value
  % also save a placeholder _Index that will instantiated by skolemise(F, _VarList, F) to the index of the clause in 
  % which the skolem term X is introduced
  % note 1: b_setval/b_getval – other than assert/retract and nb_setval/nb_getval – preserve the names of variables 
  % note 2: this approach ensures that all occurences of a skolem term get associated with the same variable
  b_setval(Functor, (CopiedX, [_Index])).


%---------------------------------------------------------------------------------------------------------
%
%  generate conjunctive normal form
%  
%  clause set compaction: conjunctions of the form (A,B) and disjunctions of the form (A;B) that were  
%  generated in the step "move negations inside" are also treated as literals
%
%---------------------------------------------------------------------------------------------------------

conjunctive_normal_form(A, A) :-					
  disjunction_of_literals(A),
  !.

conjunctive_normal_form((A & B) v C, D & E) :-	
  !,
  conjunctive_normal_form(A v C, D),
  conjunctive_normal_form(B v C, E).

conjunctive_normal_form(A v (B & C), D & E) :-	
  !,
  conjunctive_normal_form(A v B, D),
  conjunctive_normal_form(A v C, E).

conjunctive_normal_form(A & B, C & D) :-			
  !,
  conjunctive_normal_form(A, C),
  conjunctive_normal_form(B, D).

conjunctive_normal_form(A v B, E) :-				
  !,
  conjunctive_normal_form(A, C),
  conjunctive_normal_form(B, D),
  conjunctive_normal_form(C v D, E).


%---------------------------------------------------------------------------------------------------------
%
%  generate clausal form
%
%---------------------------------------------------------------------------------------------------------

clausal_form(A & B, Clauses) :-
  !,
  clausal_form(A, ClausesA),
  clausal_form(B, ClausesB),
  adjoin_body(ClausesA, ClausesB, Clauses).

clausal_form(A v B, satchmo_clause(ScrubbedBody, ScrubbedHead, Indices)) :-
  !,
  make_clause(A v B, satchmo_clause(Body, Head, Indices)),
  scrub_indices_from_body(Body, ScrubbedBody, [], IntermediateIndices),
  scrub_indices_from_head(Head, ScrubbedHead,IntermediateIndices, FinalIndices),
  sort(FinalIndices, Indices).

clausal_form(A, satchmo_clause(ScrubbedBody, ScrubbedHead, Indices)) :-
  !,
  make_clause(A, satchmo_clause(Body, Head, Indices)),
  scrub_indices_from_body(Body, ScrubbedBody, [], IntermediateIndices),
  scrub_indices_from_head(Head, ScrubbedHead,IntermediateIndices, FinalIndices),
  sort(FinalIndices, Indices).
          
make_clause(A v B, satchmo_clause(BodyAB, HeadAB, _Indices)) :-
  !,
  make_clause(A, satchmo_clause(BodyA, HeadA, _Indices)),
  make_clause(B, satchmo_clause(BodyB, HeadB, _Indices)),
  adjoin_head(HeadA, HeadB, HeadAB),
  adjoin_body(BodyA, BodyB, BodyAB).

make_clause(-N, satchmo_clause(N, fail-Index, _Indices)) :-
  conjunction_of_logical_atoms(N, _NInSatchmoNotation, Index),
  !.

make_clause(-N, satchmo_clause(N, fail-Index, _Indices)) :-
  disjunction_of_logical_atoms(N, _NInSatchmoNotation, Index),
  !.

make_clause(P, satchmo_clause(true-Index, P, _Indices)) :-
  conjunction_of_logical_atoms(P, _PInSatchmoNotation, Index),
  !.

make_clause(P, satchmo_clause(true-Index, P, _Indices)) :-
  disjunction_of_logical_atoms(P, _PInSatchmoNotation, Index),
  !.

%---------------------------------------------------------------------------------------------------------
%
%  convert clause conjunction into clause list
% 
%  skip clauses that are not range-restricted
%
%---------------------------------------------------------------------------------------------------------

convert_clause_conjunction_into_clause_list(ClauseConjunction, ClauseList) :-
  convert_clause_conjunction_into_clause_list(ClauseConjunction, [], ClauseList).

convert_clause_conjunction_into_clause_list((satchmo_clause(Body, Head, Indices), MoreConjuncts), SoFar, ClauseList) :-
  !,
  (
    range_restricted(Body, Head, Indices)
    ->
    convert_clause_conjunction_into_clause_list(MoreConjuncts, [satchmo_clause(Body, Head, Indices)|SoFar], ClauseList)
  ;
    % skip non-range-restricted clause
    convert_clause_conjunction_into_clause_list(MoreConjuncts, SoFar, ClauseList)
  ).

convert_clause_conjunction_into_clause_list(satchmo_clause(Body, Head, Indices), SoFar, ClauseList) :-
  (
    range_restricted(Body, Head, Indices)
    -> 
    ClauseList = [satchmo_clause(Body, Head, Indices)|SoFar]
  ;
    % skip non-range-restricted clause
    ClauseList = SoFar
  ).


%---------------------------------------------------------------------------------------------------------
%
%  combine clauses with Body 'true' and identical index that were split in preceding steps into separate
%  clauses 
%
%  Head must not be a conjunction or disjunction
%
%---------------------------------------------------------------------------------------------------------

combine_clauses(Clauses, CombinedClauses) :-
  combine_clauses(Clauses, [], CombinedClauses).

combine_clauses(Clauses, SoFar, CombinedClauses) :-
  (
    member(satchmo_clause(true, Head, Index), Clauses), 
    \+ Head = (_, _), 
    \+ Head = (_ ; _)
    ->
    findall(satchmo_clause(true, Head1, Index), (member(satchmo_clause(true, Head1, Index), Clauses), \+ Head1 = (_, _), \+ Head1 = (_ ; _)), SelectedClauses),
    subtract(Clauses, SelectedClauses, RestClauses),
    findall(Head1, member(satchmo_clause(true, Head1, Index), SelectedClauses), CombinedClauseHeadAsList),
    list_to_conjunction(CombinedClauseHeadAsList, CombinedClauseHead),
    combine_clauses(RestClauses, [satchmo_clause(true, CombinedClauseHead, Index)|SoFar], CombinedClauses)
  ;
    append(Clauses, SoFar, CombinedClauses)
  ).


%---------------------------------------------------------------------------------------------------------
%
%  modify clauses 
%
%  not all clauses needed for some deductions are directly derived from ACE axioms and theorems and thus 
%  must be explicitly constructed 
%
%  deactivated: case 1: 'exactly N' |- 'at least N' & 'at most N'
%  theorem 'at least N' & 'at most N' leads to a clause 'at least N' -> 'more than N' so that the clause 
%  set derived from the axiom and the theorem does not contain an implication to 'fail' necessary for the 
%  successful deduction
%  thus the clause 'at least N' -> 'more than N' is replaced by the clause 'exactly N' -> 'fail'
%  note 1: this operation may seem radical, but is in principle not different from using auxiliary axioms
%  that more indirectly provide bridges to requested deductions
%  note 2: attempts to do this operation via auxiliary axioms lead to dynamic changes of the clause set 
%  that require changes in some parts of the code of satchmo.pl
%
%  deactivated: case 2: Tweety is a bird. |- Tweety does not fly.
%  theorem 'Tweety does not fly.' leads to a clause 'object(tweety) -> fly(tweety)' so that the clause set
%  derived from the axiom and the theorem does not contain an implication to 'fail' necessary for the (non-
%  monotonic) deduction
%  thus a clause 'fly(tweety) -> fail' is added to achieve the non-monotonic result
%  note: this is an under the cover modifications that becomes visible to the user only via a warning message 
%  and can lead to incorrect further deductions; proofs that one expects to fail will succeed; user has no control 
%  over non-monotonicity since any negated theorem will be proved, however unrelated to the problem at hand
%
%  case 3: Body -> Head has the form 'naf(P1) & P2 -> fail' that will not fire if P1 and P2 have unifying object 
%  or predicate conditions; replace by "If Q then not P. If not provably P then Q." with suitable phrases P and Q.
%  example: "If a bird does not provably fly then it does not fly." is replaced by "If a bird is abnormal then 
%  it does not fly. If a bird does not provably fly then it is abnormal."
%  note: check whether the tests for the overlap of P1 and P2 are adequate and sufficient

%---------------------------------------------------------------------------------------------------------
/* 
% case 1 deactivated as superfluous
modify_clause_set(Clauses, ModifiedClauses) :-
  (
    select(satchmo_clause(Body, Head, Indices), Clauses, IntermediateClauses1),
    support:subterm(object(World, _Referent1, Noun, countable, na, geq, N), Body),
    support:subterm(object(World, _Referent2, Noun, countable, na, greater, N), Head)
    ->
    modify_one_clause(satchmo_clause(Body, Head, Indices), IntermediateClauses1, IntermediateClauses2),
    modify_clause_set(IntermediateClauses2, ModifiedClauses)  
  ;
    ModifiedClauses = Clauses
  ).

modify_one_clause(satchmo_clause(Body, Head, Indices), IntermediateClauses1, IntermediateClauses2) :-
  (
    support:subterm(object(World, Referent1, Noun, countable, na, geq, N), Body),
    support:subterm(object(World, _Referent2, Noun, countable, na, greater, N), Head)
    ->
    substitute(object(World, Referent1, Noun, countable, na, geq, N), object(World, Referent1, Noun, countable, na, exactly, N), Body, NewBody), 
    modify_one_clause(satchmo_clause(NewBody, Head, Indices), IntermediateClauses1, IntermediateClauses2)
  ;
    IntermediateClauses2 =  [satchmo_clause(Body, fail, Indices) | IntermediateClauses1]
  ).
*/

/*
% case 2 deactivated: this is an under the cover modification that becomes visible to the user only via a warning  
% message and can lead to incorrect further deductions; proofs that one expects to fail will succeed; most importantly:
% user has no control over non-monotonicity since any negated theorem will be proved, however unrelated to the problem at hand

modify_clause_set(Clauses, ModifiedClauses) :-
  ( 
    member(satchmo_clause(Body, Head, Index), Clauses),
    \+ Head = fail,
    member(theorem(_), Index),  
    \+ member(satchmo_clause(Head, fail, [axiom(_)|_]), Clauses)
    ->
    add_warning_message_once(race, '', 'Non-monotonic reasoning: The theorem can be proved since in the axioms there is no explicit information to the contrary.', 'Check axioms.'),
    ModifiedClauses = [satchmo_clause(Head, fail, Index) | Clauses]
  ;
    ModifiedClauses = Clauses
  ).
*/

:- user:dynamic(abnormal/0).

modify_clause_set(Clauses, ModifiedClauses) :-
  ( 
	% clause is an implication 'naf(P1) & P2 -> fail' that may not fire if P1 and P2 sufficiently overlap
    select(satchmo_clause(Body, fail, Index), Clauses, RestClauses),
	conjunction_to_list(Body, BodyAsList),
	% Body contains a NAF term
	select(naf(NAFList), BodyAsList, RestBodyAsList),
    (
	  % NAF term contains a predicate condition that unifies with one in RestBodyAsList
	  member(Predicate1, NAFList),
	  Predicate1 =.. [predicate|Arguments1],
	  % RestBodyAsList contains a predicate condition
	  member(Predicate2, RestBodyAsList),
	  Predicate2 =.. [predicate|Arguments2],
	  % predicate conditions are unifiable without creating cyclic terms
      \+ \+ unify_with_occurs_check(Arguments1, Arguments2)
    ;
	  % NAF term contains an object condition that unifies with one in RestBodyAsList
	  member(Object1, NAFList),
	  Object1 =.. [object|Arguments1],
	  % RestBodyAsList contains a predicate condition
	  member(Object2, RestBodyAsList),
	  Object2 =.. [object|Arguments2],
	  % object conditions are unifiable without creating cyclic terms
      \+ \+ unify_with_occurs_check(Arguments1, Arguments2)
    )
	->
	% create two new clauses linked by a fictitious condition "abnormal"
	list_to_conjunction([abnormal | RestBodyAsList], NewRestBody),
	% get conditions that are in RestBodyAsList but not in NAFList
	subtract(RestBodyAsList, NAFList, DifferentElements),
	(
	  DifferentElements \= []
	  ->
	  list_to_conjunction(DifferentElements, DifferentElementsAsConjunction),
	  IntermediateClauses = [satchmo_clause((DifferentElementsAsConjunction, naf(NAFList)), abnormal, Index), 
	  satchmo_clause(NewRestBody, fail, Index) | RestClauses]
	;
	  % DifferentElements = []
	  IntermediateClauses = [satchmo_clause(naf(NAFList), abnormal, Index), 
	  satchmo_clause(NewRestBody, fail, Index) | RestClauses]
	),
	modify_clause_set(IntermediateClauses, ModifiedClauses)
  ;
    ModifiedClauses = Clauses
  ).


%---------------------------------------------------------------------------------------------------------
%
%  remove_underspecification(UnderspecifiedClauses, Clauses)
%
%  DRS derived from ACE texts contains underspecified conditions some of which need to be substantiated;
%  furthermore some constructs need to be transformed
%
%  interpret_copula/2
%
%    with an integer or a real number as at least one argument
%    replace copula by equivalent formula
%    marking: be --> =
%
%    with modifiers as in "... strenuously is a busy student in the morning." or "... seriously is rich 
%    in the beginning." to prevent the derivation without the modifiers "... is a (busy) student." or 
%    " ... is rich."
%    marking: be --> be_MOD
%
%    with two proper names as in "John is Mary." to allow all inferences regarding
%    "John" to be carried over to "Mary"
%    marking: be --> be_ID
%
%    with one proper name and somebody/something as in "somebody is Mary." to allow 
%    inferences from "somebody/something" to be carried over to "Mary"
%    marking: be --> be_ID
%
%    with noun phrase as second argument as in "... is a busy student." to allow 
%    the inference "... is a (busy) student."
%    marking: be --> be_NP
%
%    with intransitive predicative adjective as in "... a man is rich ..." to allow
%    to derive "... a rich man ...."
%    marking: be --> be_ADJ
%
%
%  reconstruct_whose/2
%
%    replace query(World, Referent, what) plus genitive by query(World, Referent, whose)
%
%
%  generalise_which/2
%
%    if "which" plus countable noun is found then specialise "which" with the noun and replace
%    countable nouns by a generalised version that matches both countable and mass nouns
%
%  
%  add_role_to_of_relation/2
%
%    replace relation(World, Referent1, of, Referent2) and object(World, Referent1, Noun, ...) by 
%    relation(World, Referent1, Noun, of, Referent2) and object(World, Referent1, Noun, ...)
%
%  
%  specialise_howm/2
%
%    replace howm by how_many, respectively how_much
%
%
%  complete_disjunctions_of_formulas/2
%
%    disjunctions of formulas like 'A is 1 or A is 2.' used as theorems lead to two clauses
% 
%    satchmo_clause((object(sk1, _G5147, something, dom, na, na, na), formula(sk1, _G5147, =, int(1))), fail, [theorem(1)])
%    satchmo_clause(formula(sk1, _G5147, =, int(2)), fail, [theorem(1)])
%
%    one of which contains an object definition that ensures that the variable of the formula is instantiated 
%    in time by satchmo:prove_body/4, while the other clause consists only of a formula whose variable would 
%    not be instantiated leading later to an instantiation error in functor/3
%
%    complete_disjunctions_of_formulas/2 copies the missing object definition to the clause that consists only
%    of a formula
%
%
%  replace_quadratic_equation_by_solutions/2
%
%    quadratic equations X^2 + P*X + Q = 0 cannot be solved directly by CLPQR that satchmo/3 uses for arithmetic
%    transform them into their two solutions - (P/2) +/- ((P/2)^2 - Q)^(1/2) that CLPQR can handle
%    since the transformation assumes that the parameters P and Q are positive make case distinctions for 
%    the actual values of P and Q
%    generate an error message if (P/2)^2 - Q is negative so that the square root would be imaginary
%
%---------------------------------------------------------------------------------------------------------
  
remove_underspecification(UnderspecifiedClauses, Clauses) :-
  interpret_copula(UnderspecifiedClauses, IntermediateClauses1),
  reconstruct_whose(IntermediateClauses1, IntermediateClauses2),
  generalise_which(IntermediateClauses2, IntermediateClauses3),
  add_role_to_of_relation(IntermediateClauses3, IntermediateClauses4),
  specialise_howm(IntermediateClauses4, IntermediateClauses5),
  complete_disjunctions_of_formulas(IntermediateClauses5, IntermediateClauses6),
  replace_quadratic_equation_by_solutions(IntermediateClauses6, Clauses).

/* deprecated
interpret_copula_with_numbers_and_expressions(Clauses, NewClauses) :-
  support:subterm(predicate(World, A, be, B, C), Clauses),
  (
    % left argument is a number or an expression
    nonvar(B),
    (B = int(_) ; B = real(_) ; B = expr(_, _, _))
    ->
    substitute(predicate(World, A, be, B, C), formula(World, B, =, C), Clauses, IntermediateClauses),     
    interpret_copula_with_numbers_and_expressions(IntermediateClauses, NewClauses)
  ;
    % right argument is a number or an expression
    nonvar(C),
    (C = int(_) ; C = real(_) ; C = expr(_, _, _))
    ->
    substitute(predicate(World, A, be, B, C), formula(World, B, =, C), Clauses, IntermediateClauses),     
    interpret_copula_with_numbers_and_expressions(IntermediateClauses, NewClauses)
  ;
    % no (further) formula
    NewClauses = Clauses
  ).

interpret_copula_with_numbers(Clauses, NewClauses) :-
  support:subterm(predicate(World, A, be, B, C), Clauses),
  (
    % left argument is a skolem term, right argument is a number: substitute left argument by right argument
    nonvar(C),
    (C = int(Number) ; C = real(Number)), 
    nonvar(B), 
    functor(B, Functor, _Arity), 
    \+ Functor = [], 
    sub_atom(Functor, 0, _, _, sk)
    ->
    substitute(B, C, Clauses, IntermediateClauses),
    % label copula
    substitute(predicate(World, A, be, C, C), predicate(World, A, be_NP, C, C), IntermediateClauses, NewClauses)
  ;
    % right argument is a skolem term, left argument is a number: substitute right argument by left argument
    nonvar(B), 
    (B = int(Number) ; B = real(Number)), 
    nonvar(C), 
    functor(C, Functor, _Arity), 
    \+ Functor = [],
    sub_atom(Functor, 0, _, _, sk)
    ->
    substitute(C, B, Clauses, IntermediateClauses),
    % label copula
    substitute(predicate(World, A, be, B, B), predicate(World, A, be_NP, B, B), IntermediateClauses, NewClauses)
  ;
    % both left and right argument are integers or reals
    nonvar(B), 
    (B = int(NumberB) ; B = real(NumberB)), 
    nonvar(C),
    (C = int(NumberC) ; C = real(NumberC)),
    (
      % both numbers have the same value
      NumberB = NumberC
      -> 
      % label copula
      substitute(predicate(World, A, be, B, C), predicate(World, A, be_NP, B, C), Clauses, NewClauses)
    ;
      % both numbers have different values and ...
      (
        % ... copula occurs in a clause with Head ≠ fail
        \+ Head = fail
        ->
        % create error message
        Index = [SourceSentenceNumber],
        SourceSentenceNumber =.. [Source, SentenceNumber],
        atomic_list_concat(['In ', Source, ' ', SentenceNumber, ' the numbers ', NumberB, ' and ', NumberC, ' are erroneously claimed to be identical which leads to inconsistency.'], MessageText),
        add_error_message(race, SentenceNumber-'', MessageText, 'Check input.')
      ;
        % ... copula occurs in a clause with Head = fail
        true
      ),
      % label copula
      substitute(predicate(World, A, be, B, C), predicate(World, A, be_NP, B, C), Clauses, NewClauses)
    )
  ).

interpret_copula_with_expressions(Clauses, NewClauses) :-
  (
    % find copula with expression as argument
    support:subterm(predicate(World, A, be, B, C), Clauses),
    (B = expr(_, _, _) ; C = expr(_, _, _))
    ->
    % label copula, evaluate expression and substitute left and right argument by value of expression 
    substitute(predicate(World, A, be, B, C), predicate(World, A, be_NUM, B, C), Clauses, IntermediateClauses),
    substitute(predicate(World, A, be, B, C), predicate(World, A, be_NUM, B, C), Clauses, IntermediateClauses),
    evaluate(C, C, Index, Value),
    substitute(B, Value, IntermediateClauses1, IntermediateClauses2),
    substitute(C, Value, IntermediateClauses2, IntermediateClauses),
    % continue loop
    interpret_copula_with_expressions(IntermediateClauses, NewClauses)
  ;
    % no (further) copula
    NewClauses = Clauses
  ).

interpret_formulas(Clauses, NewClauses) :-
  (
    support:subterm(formula(Operand1, Operator, Operand2), Clauses)
    ->
    Predicate =.. [Operator, Operand1, Operand2],
    substitute(formula(Operand1, Operator, Operand2), Predicate, Clauses, IntermediateClauses),
    interpret_formulas(IntermediateClauses, NewClauses)
  ;
    % no (further) formula
    NewClauses = Clauses
  ).
*/

interpret_copula(Clauses, NewClauses) :-
  (
    % copula ...
    support:subterm(predicate(World, A, be, B, C), Clauses),
    (
      % ... with modifier
      % all cases with modifiers are caught here, all other cases do not have modifiers
      (
        support:subterm(modifier_pp(World, Referent, _Preposition, _Noun), Clauses),
        % exclude case of copula & adjective & prepositional phrase as in "...is located in ...",
        % and treat this case later as adjective
        % referent of adjective is C
        \+ support:subterm(property(World, C, _Adjective, _Degree), Clauses)
      ; 
        support:subterm(modifier_adv(World, Referent, _Adverb, _Degree), Clauses)
      ),
      Referent == A
      ->
      substitute(predicate(World, A, be, B, C), predicate(World, A, be_MOD, B, C), Clauses, IntermediateClauses)
    ;
      % ... numbers or expressions
	  (
		% left argument is a number or an expression
		nonvar(B),
		(B = int(_) ; B = real(_) ; B = expr(_, _, _))
		->
		% replace by equivalent formula
		substitute(predicate(World, A, be, B, C), formula(World, B, =, C), Clauses, IntermediateClauses),
		% referent A that is dropped in this transformation can occur as argument in other skolem terms
		% skolemise A if it is a variable because otherwise there will be incompletely instantiated terms violating range restriction
		(
		  var(A)
		  ->
		  % create Skolem term
          once(retract(skolem_counter(N))),
          N1 is N + 1,
          assert(skolem_counter(N1)),
          name(N, CharList), 								
          name(A, [115,107|CharList])
        ;
          true
        )
	  ;
		% right argument is a number or an expression
		nonvar(C),
		(C = int(_) ; C = real(_) ; C = expr(_, _, _))
		->
		% replace by equivalent formula
		substitute(predicate(World, A, be, B, C), formula(World, B, =, C), Clauses, IntermediateClauses),     
		% referent A that is dropped in this transformation can occur as argument in other skolem terms
		% skolemise A if it is a variable because otherwise there will be incompletely instantiated terms violating range restriction
		(
		  var(A)
		  ->
		  % create Skolem term
          once(retract(skolem_counter(N))),
          N1 is N + 1,
          assert(skolem_counter(N1)),
          name(N, CharList), 								
          name(A, [115,107|CharList])
        ;
          true
        )
	  )
    ;
      % ... with two proper names or somebody/something and one proper name
      (
        % John is Harry.
        support:subterm(object(World, ReferentB, _NameB, named, na, eq, 1), Clauses),
        ReferentB == B,
        support:subterm(object(World, ReferentC, _NameC, named, na, eq, 1), Clauses),
        ReferentC == C
      ;
        % John is somebody/something.
        support:subterm(object(World, ReferentB, _NameB, named, na, eq, 1), Clauses),
        ReferentB == B,
        (
          support:subterm(object(World, ReferentC, somebody, countable, na, eq, 1), Clauses)
        ;
          support:subterm(object(World, ReferentC, something, dom, na, na, na), Clauses)
        ),
        ReferentC == C
      ;
        % Somebody/something is John.
        support:subterm(object(World, ReferentC, _NameC, named, na, eq, 1), Clauses),
        ReferentC == C,
        (
          support:subterm(object(World, ReferentB, somebody, countable, na, eq, 1), Clauses)
        ;
          support:subterm(object(World, ReferentB, something, dom, na, na, na), Clauses)
        ),
        ReferentB == B
      ;
        % Somebody is something.
        support:subterm(object(World, Referent1, somebody, countable, na, eq, 1), Clauses),
        support:subterm(object(World, Referent2, something, dom, na, na, na), Clauses),
        Referent1 == B,
        Referent2 == C
      ;
        % Something is somebody.
        support:subterm(object(World, Referent1, something, dom, na, na, na), Clauses),
        support:subterm(object(World, Referent2, somebody, countable, na, eq, 1), Clauses),
        Referent1 == B,
        Referent2 == C
      ;
        % Something is something.
        support:subterm(object(World, Referent1, something, dom, na, na, na), Clauses),
        support:subterm(object(World, Referent2, something, dom, na, na, na), Clauses),
        Referent1 == B,
        Referent2 == C
      ) 
      ->
      substitute(predicate(World, A, be, B, C), predicate(World, A, be_ID, B, C), Clauses, IntermediateClauses)
    ;
      % see also Prolog axiom c1c
      % ... with an implication of the form "every countable NP1 is a countable NP2" but ...
      % ... not with an implication of the form "no countable NP1 is a countable NP2"
      % APE generates implications where the object conditions have the cardinality "geq 1". 
      % This does not allow to use the implications with other cardinalities. Thus the cardinalities are
      % replaced by variables.
      member(satchmo_clause(Body, Head, _Index), Clauses), 
      \+ Head = fail,
      support:subterm(predicate(World, Referent, be, Subject, Object), Head),
      var(Subject),
      support:subterm(object(World, Referent1, Noun1, countable, na, GEQ, One), Body),
      % make sure that all cardinalities of the implication are replaced by the same variables
      ((var(GEQ), var(One) -> (EQ = GEQ, N = One)) ; (GEQ == geq, One == 1)),
      var(Referent1),
      Referent1 == Subject,
      support:subterm(object(World, Referent2, Noun2, countable, na, geq, 1), Head),
      Referent2 == Object
      ->
      substitute(predicate(World, Referent, be, Subject, Object), predicate(World, Referent, be_NP, Subject, Object), Clauses, IntermediateClauses1),
      substitute(object(World, Referent1, Noun1, countable, na, geq, 1), object(World, Referent1, Noun1, countable, na, EQ, N), IntermediateClauses1, IntermediateClauses2),
      substitute(object(World, Referent2, Noun2, countable, na, geq, 1), object(World, Referent2, Noun2, countable, na, EQ, N), IntermediateClauses2, IntermediateClauses)
    ;
      % see also Prolog axiom c1m
      % ... with an implication of the form "all mass NP1 is some mass NP2" but ...
      % ... not with an implication of the form "It is false that some mass NP1 is some mass NP2"
      member(satchmo_clause(Body, Head, _Index), Clauses), 
      \+ Head = fail,
      support:subterm(predicate(World, Referent, be, Subject, Object), Head),
      var(Subject),
      support:subterm(object(World, Referent1, Noun1, mass, Measure1, EQ1, Count1), Body),
      var(Referent1),
      Referent1 == Subject,
      support:subterm(object(World, Referent2, Noun2, mass, Measure2, EQ2, Count2), Head),
      Referent2 == Object
      ->
      substitute(predicate(World, Referent, be, Subject, Object), predicate(World, Referent, be_NP, Subject, Object), Clauses, IntermediateClauses1),
      substitute(object(World, Referent1, Noun1, mass, Measure1, EQ1, Count1), object(World, Referent1, Noun1, mass, Measure, EQ, N), IntermediateClauses1, IntermediateClauses2),
      substitute(object(World, Referent2, Noun2, mass, Measure2, EQ2, Count2), object(World, Referent2, Noun2, mass, Measure, EQ, N), IntermediateClauses2, IntermediateClauses)
    ;
      % ... with countable noun phrase – other than somebody – as first argument and common noun phrase as second argument
      support:subterm(object(World, Referent, _Noun, countable, na, _EQ, _Count), Clauses), 
      (
        % A man is John/a human/somebody/something.
        Referent == B,
        % exclude predicative transitive adjective
        \+ (support:subterm(property(World, Referent2, _Adjective, _Degree), Clauses), Referent2 == C)
      ;
        % John/a human/somebody/something is a man.
        Referent == C
      )
      ->
      substitute(predicate(World, A, be, B, C), predicate(World, A, be_NP, B, C), Clauses, IntermediateClauses)
    ;
      % ... with mass noun phrase as first argument and common noun phrase as second argument
      % All water is a fluid.
      support:subterm(object(World, Referent, _Noun, mass, _Measure, _EQ, _Count), Clauses), 
      (Referent == B ; Referent == C),
      % exclude predicative transitive adjective
      \+ (support:subterm(property(World, Referent2, _Adjective, _Degree), Clauses), Referent2 == C)
      ->
      substitute(predicate(World, A, be, B, C), predicate(World, A, be_NP, B, C), Clauses, IntermediateClauses)
/* substituted by code above (line 657)  
    ;
      % ... with a number or expression as at least one argument
      % A is 3. 3.14 is Pi. X is Y+1.
%%%%%%      \+ \+ (B == int(_) ; B == real(_) ; B == expr(_,_,_) ; C == int(_) ; C == real(_) ; C == expr(_,_,_))
%%%%%% NOTE 28AUG2012: this substitution needs to be checked because it may invalidate some test cases
      \+ \+ (B = int(_) ; B = real(_) ; B = expr(_,_,_) ; C = int(_) ; C = real(_) ; C = expr(_,_,_))
      ->
      substitute(predicate(World, A, be, B, C), predicate(World, A, be_NP, B, C), Clauses, IntermediateClauses)
*/
    ;
      % ... with predicative transitive adjective
      % A man is tall.
      support:subterm(property(World, Referent, _Adjective, _Degree), Clauses),
      Referent == C
      ->
      substitute(predicate(World, A, be, B, C), predicate(World, A, be_ADJ, B, C), Clauses, IntermediateClauses)
    ;
      % ... with query word who or what as at least one argument
      % Who is what?
      (support:subterm(query(World, Referent, who), Clauses) ; support:subterm(query(World, Referent, what), Clauses)), 
      (Referent == B ; Referent == C)
      ->
      substitute(predicate(World, A, be, B, C), predicate(World, A, be_NP, B, C), Clauses, IntermediateClauses)
    ),
    % continue loop
    interpret_copula(IntermediateClauses, NewClauses)
  ;
   % no (further) copula
   NewClauses = Clauses
  ).


reconstruct_whose(Clauses, NewClauses) :-
  (
    % "whose" represented as "of what" found
    support:subterm(query(World, Referent1, what), Clauses),
    support:subterm(relation(World, _Referent2, of, Referent3), Clauses),
    Referent3 == Referent1
    ->
    substitute(query(World, Referent1, what), query(World, Referent1, whose), Clauses, IntermediateClauses),
    % continue loop
    reconstruct_whose(IntermediateClauses, NewClauses)
  ;
   % no (further) "whose"
   NewClauses = Clauses
  ).
  

generalise_which(Clauses, NewClauses) :-
  (
    % "which" plus countable noun found
    member(satchmo_clause(Body, Head, Index), Clauses),
    support:subterm(query(World, Referent1, which), Body),
    support:subterm(object(World, Referent2, Noun, countable, na, EQ, Counter), Body), 
    Referent1 == Referent2
    ->
    % eliminate the clause
    select(satchmo_clause(Body, Head, Index), Clauses, RestClauses),
    % specialise "which" with following noun
    substitute(query(World, Referent1, which), query(World, Referent1, which(Noun)), Body, IntermediateBody),
    % replace countable noun by a generalised noun that matches both countable and mass nouns
    substitute(object(World, Referent2, Noun, countable, na, EQ, Counter), object(World, Referent2, Noun, _Domain, _NA, _EQ, _Counter), IntermediateBody, NewBody),
    % add a new clause with NewBody
    append([satchmo_clause(NewBody, Head, Index)], RestClauses, IntermediateClauses),
    % continue loop
    generalise_which(IntermediateClauses, NewClauses)
  ;
    % no (further) "which"
    NewClauses = Clauses
  ).

  
add_role_to_of_relation(Clauses, NewClauses) :-
  (
    % "of"-relation found
    support:subterm(relation(World, Referent1, of, Referent2), Clauses),
    support:subterm(object(World, Referent3, Noun, _Domain, na, _EQ, _Num), Clauses),
    Referent3 == Referent1
    ->
    substitute(relation(World, Referent1, of, Referent2), relation(World, Referent1, Noun, of, Referent2), Clauses, IntermediateClauses),
    % continue loop
    add_role_to_of_relation(IntermediateClauses, NewClauses)
  ;
   % no (further) "of"-relation
   NewClauses = Clauses
  ).

/*
specialise_howm(Clauses, NewClauses) :-
  (
    % "howm" found
    member(satchmo_clause(Body, fail, Index), Clauses),
    support:subterm(query(World, Referent1, howm), Body)
    ->
    % eliminate the clause
    select(satchmo_clause(Body, fail, Index), Clauses, RestClauses),
    (
      % "howm" plus countable noun
      support:subterm(object(World, Referent2, Noun, countable, na, geq, 2), Body),
      Referent1 == Referent2
      ->
      % replace the cardinality 2 of the countable noun by a variable to match both singular and plural nouns
      substitute(object(World, Referent2, Noun, countable, na, geq, 2), object(World, Referent2, Noun, countable, na, geq, _Cardinality), Body, IntermediateBody),
      % eliminate query/3
      eliminate_conjunct(IntermediateBody, query(World, Referent1, howm), NewBody),
      % add a new clause whose body is only query/3 where "howm" is replaced by "how_many(NewBody)"
      append([satchmo_clause(query(World, Referent1, how_many(NewBody)), fail, Index)], RestClauses, IntermediateClauses)
    ;
      % "howm" plus mass noun
      support:subterm(object(World, Referent2, Noun, mass, na, na, na), Body),
      Referent1 == Referent2
      ->
      % replace the 3 na's of the mass noun by variables to match both mass and measurement nouns
      substitute(object(World, Referent2, Noun, mass, na, na, na), object(World, Referent2, Noun, mass, _Measure, _EQ, _Number), Body, IntermediateBody),
      % eliminate query/3
      eliminate_conjunct(IntermediateBody, query(World, Referent1, howm), NewBody),
      % add a new clause whose body is only query/3 where "howm" is replaced by "how_much(NewBody)"
      append([satchmo_clause(query(World, Referent1, how_much(NewBody)), fail, Index)], RestClauses, IntermediateClauses)
    ),
    % continue loop
    specialise_howm(IntermediateClauses, NewClauses)
  ;
    % no (further) "howm"
    NewClauses = Clauses
  ).
*/
%%%%%%
specialise_howm(Clauses, NewClauses) :-
  (
    % "howm" found
    member(satchmo_clause(Body, fail, Index), Clauses),
    support:subterm(query(World, Referent1, howm), Body)
    ->
    % eliminate the clause
    select(satchmo_clause(Body, fail, Index), Clauses, RestClauses),
    (
      % "howm" plus countable noun
      support:subterm(object(World, Referent2, Noun, countable, na, geq, 2), Body),
      Referent1 == Referent2
      ->
      % eliminate query/3 from Body
      eliminate_conjunct(Body, query(World, Referent1, howm), IntermediateBody),
      % eliminate object(World, Referent2, Noun, countable, na, geq, 2) from Body
      eliminate_conjunct(IntermediateBody, object(World, Referent2, Noun, countable, na, geq, 2), RestBody),
      % add a new clause whose body consists of a modified form of query/3 and RestBody
      % howm is replaced by how_many(object(World, Referent2, Noun, countable, na, geq, _Cardinality))
      % Noun's cardinality 2 is replaced by a variable to match both singular and plural nouns
      % eliminate spurious RestBody "true"
      (
        RestBody = true
        ->
        append([satchmo_clause(query(World, Referent1, how_many(object(World, Referent2, Noun, countable, na, geq, _Cardinality))), fail, Index)], RestClauses, IntermediateClauses)
      ;
        append([satchmo_clause((query(World, Referent1, how_many(object(World, Referent2, Noun, countable, na, geq, _Cardinality))), RestBody), fail, Index)], RestClauses, IntermediateClauses)
      )
    ;
      % "howm" plus mass noun
      support:subterm(object(World, Referent2, Noun, mass, na, na, na), Body),
      Referent1 == Referent2
      ->
      % eliminate query/3 from Body
      eliminate_conjunct(Body, query(World, Referent1, howm), IntermediateBody),
      % eliminate object(World, Referent2, Noun, mass, na, na, na) from Body
      eliminate_conjunct(IntermediateBody, object(World, Referent2, Noun, mass, na, na, na), RestBody),
      % add a new clause whose body consists of a modified form of query/3 and RestBody
      % howm is replaced by how_many(object(World, Referent2, Noun, countable, na, geq, _Cardinality))
      % Noun's 3 na'sare replaced by variables to match both mass and measurement nouns
      % eliminate spurious RestBody "true"
      (
        RestBody = true
        ->
        append([satchmo_clause(query(World, Referent1, how_much(object(World, Referent2, Noun, mass, _Measure, _EQ, _Number))), fail, Index)], RestClauses, IntermediateClauses)
      ;
        append([satchmo_clause((query(World, Referent1, how_much(object(World, Referent2, Noun, mass, _Measure, _EQ, _Number))), RestBody), fail, Index)], RestClauses, IntermediateClauses)
      )
    ),
    % continue loop
    specialise_howm(IntermediateClauses, NewClauses)
  ;
    % no (further) "howm"
    NewClauses = Clauses
  ).

/* 
specialise_howm(Clauses, NewClauses) :-
  (
    % "howm" found
    member(satchmo_clause(Body, fail, Index), Clauses),
    support:subterm(query(World, Referent, howm), Body)
    ->
    % eliminate the clause
    select(satchmo_clause(Body, fail, Index), Clauses, RestClauses),
    (
      % "howm" plus countable noun
      support:subterm(object(World, Referent, Noun, countable, na, geq, 2), Body)
      ->
      % specialise "howm" with Body of clause without query condition
      eliminate_conjunct(Body, query(World, Referent, howm), RestBody),
      % replace Noun's cardinality 2 by a variable to match both singular and plural nouns
      substitute(object(World, Referent, Noun, countable, na, geq, 2), object(World, Referent, Noun, countable, na, geq, _Cardinality), RestBody, NewBody),
      % add a new clause with NewBody
      append([satchmo_clause(query(World, Referent, how_many(NewBody)), fail, Index)], RestClauses, IntermediateClauses)
    ;
      % "howm" plus mass noun
      support:subterm(object(World, Referent, Noun, mass, na, na, na), Body)
      ->
      % specialise "howm" with Body of clause without query condition
      eliminate_conjunct(Body, query(World, Referent, howm), RestBody),
      % replace Noun's 3 na's by variables to match both mass and measurement nouns
      substitute(object(World, Referent, Noun, mass, na, na, na), object(World, Referent, Noun, mass, _Measure, _EQ, _Number), RestBody, NewBody),
      % add a new clause with NewBody
      append([satchmo_clause(query(World, Referent, how_much(NewBody)), fail, Index)], RestClauses, IntermediateClauses)
    ),
    % continue loop
    specialise_howm(IntermediateClauses, NewClauses)
  ;
    % no (further) "howm"
    NewClauses = Clauses
  ).
*/

complete_disjunctions_of_formulas(Clauses, NewClauses) :-
  complete_disjunctions_of_formulas(Clauses, Clauses, [], NewClauses).

complete_disjunctions_of_formulas([], _Clauses, NewClauses, NewClauses).

complete_disjunctions_of_formulas([Clause|Clauses], ClausesIn, ClausesSofar, ClausesOut) :-
  (
    Clause = satchmo_clause(formula(World, LHS, Op, RHS), fail, Index),
    member(satchmo_clause(Body, fail, Index), ClausesIn),
    Body \== formula(World, LHS, Op, RHS)
    -> 
    support:subterm(formula(World, _LHS, _Op, _RHS), Body),
    support:subterm(object(World, Referent, Noun, Class, Unit, Operator, Count), Body),
    complete_disjunctions_of_formulas(Clauses, ClausesIn, [satchmo_clause((formula(World, LHS, Op, RHS), object(World, Referent, Noun, Class, Unit, Operator, Count)), fail, Index)|ClausesSofar], ClausesOut)
  ;
    complete_disjunctions_of_formulas(Clauses, ClausesIn, [Clause|ClausesSofar], ClausesOut)
  ).


replace_quadratic_equation_by_solutions(OriginalClauses, NewClauses) :-
  replace_quadratic_equation_by_solutions(OriginalClauses, OriginalClauses, [], NewClauses).
  
replace_quadratic_equation_by_solutions(_OriginalClauses, [], NewClauses, NewClauses). 

replace_quadratic_equation_by_solutions(OriginalClauses, [Clause|Clauses], ClausesSofar, ClausesOut) :-
  replace_quadratic_equation_by_solutions_in_one_clause(OriginalClauses, Clause, NewClause),
  replace_quadratic_equation_by_solutions(OriginalClauses, Clauses, [NewClause|ClausesSofar], ClausesOut).
/*  
replace_quadratic_equation_by_solutions_in_one_clause(satchmo_clause(Body, Head, Index), NewClause) :-
  (
    % there is a formula LHS=0 where LHS is a quadratic expression X^2 + P*X + Q
    support:subterm(formula(World, LHS, =, int(0)), (Body, Head)), 
    is_quadratic_expression(LHS, Skolem, P, Q)
    ->
    replace_by_solutions(Body, Head, Index, formula(World, LHS, =, int(0)), Skolem, P, Q, NewBody, NewHead),
    replace_quadratic_equation_by_solutions_in_one_clause(satchmo_clause(NewBody, NewHead, Index), NewClause)
  ;
    % there is no formula LHS=0 or LHS is not a quadratic expression X^2 + P*X + Q
    NewClause = satchmo_clause(Body, Head, Index)
  ). 
*/

replace_quadratic_equation_by_solutions_in_one_clause(OriginalClauses, satchmo_clause(Body, Head, Index), NewClause) :-
  (
    % there is a formula LHS=0 where LHS is a quadratic expression X^2 + P*X + Q
    support:subterm(formula(World, LHS, =, int(0)), Head),
    LHS = expr(_Operator, _Term1, _Term2), 
    is_quadratic_expression(LHS, Skolem, P, Q)
    ->
    replace_by_solutions(OriginalClauses, Head, Index, formula(World, LHS, =, int(0)), Skolem, P, Q, NewHead),
    replace_quadratic_equation_by_solutions_in_one_clause(OriginalClauses, satchmo_clause(Body, NewHead, Index), NewClause)
  ;
    % there is no formula LHS=0 or LHS is not a quadratic expression X^2 + P*X + Q
    NewClause = satchmo_clause(Body, Head, Index)
  ). 

is_quadratic_expression(LHS, Skolem, PP, QQ) :-
  % variable is represented as skolem constant Skolem
  support:subterm(Skolem, LHS), 
  functor(Skolem, Functor, _), 
  \+ Functor = [],
  sub_atom(Functor, 0, _, _, sk),
  (
    % case: X^2 + P*X + Q = 0
    LHS = expr(+, expr(+, expr(^, Skolem, int(2)), expr(*, P, Skolem)), Q)
    ->
    convert(P, PP),
    convert(Q, QQ)
  ;
    % case: X^2 + X + Q = 0
    LHS = expr(+, expr(+, expr(^, Skolem, int(2)), Skolem), Q)
    ->
    PP = 1,
    convert(Q, QQ)
  ;
    % case: X^2 - P*X + Q = 0
    LHS = expr(+, expr(-, expr(^, Skolem, int(2)), expr(*, P, Skolem)), Q)
    ->
    convert(P, CP), PP = -CP,
    convert(Q, QQ)
  ;
    % case: X^2 - X + Q = 0
    LHS = expr(+, expr(-, expr(^, Skolem, int(2)), Skolem), Q)
    ->
    PP = -1,
    convert(Q, QQ)
  ;
    % case: X^2 + P*X - Q = 0
    LHS = expr(-, expr(+, expr(^, Skolem, int(2)), expr(*, P, Skolem)), Q) 
    ->
    convert(P, PP),
    convert(Q, CQ), QQ = -CQ
  ;
    % case: X^2 + X - Q = 0
    LHS = expr(-, expr(+, expr(^, Skolem, int(2)), Skolem), Q) 
    ->
    PP = 1,
    convert(Q, CQ), QQ = -CQ
  ;
    % case: X^2 - P*X - Q = 0
    LHS = expr(-, expr(-, expr(^, Skolem, int(2)), expr(*, P, Skolem)), Q)  
    ->
    convert(P, CP), PP = -CP,
    convert(Q, CQ), QQ = -CQ
  ;
    % case: X^2 - X + Q = 0
    LHS = expr(-, expr(-, expr(^, Skolem, int(2)), Skolem), Q)  
    ->
    PP = -1,
    convert(Q, CQ), QQ = -CQ
  ;
    % case: X^2 + P*X = 0
    LHS = expr(+, expr(^, Skolem, int(2)), expr(*, P, Skolem))
    ->
    convert(P, PP),
    QQ = 0
  ;
    % case: X^2 + X = 0
    LHS = expr(+, expr(^, Skolem, int(2)), Skolem)
    ->
    PP = 1,
    QQ = 0
  ;
    % case: X^2 - P*X = 0
    LHS = expr(-, expr(^, Skolem, int(2)), expr(*, P, Skolem)) 
    ->
    convert(P, CP), PP = -CP,
    QQ = 0
  ;
    % case: X^2 - X = 0
    LHS = expr(-, expr(^, Skolem, int(2)), Skolem) 
    ->
    PP = -1,
    QQ = 0
  ;
    % case: X^2 + Q = 0 
    LHS = expr(+, expr(^, Skolem, int(2)), Q)
    ->
    PP = 0, 
    convert(Q, QQ)
  ;
    % case: X^2 - Q = 0
    LHS = expr(-, expr(^, Skolem, int(2)), Q) 
    ->
    PP = 0, 
    convert(Q, CQ), QQ = -CQ
  ;
    % case: X^2 = 0
    LHS = expr(^, Skolem, int(2)) 
    ->
    PP = 0, 
    QQ = 0
  ;
    % all other cases are not accepted
    add_error_message_once(race, '', 'Quadratic equations must have the form X^2 + P*X + Q = 0. P and Q are positive or negative integers, integer fractions or reals. One or both of the two terms P*X and Q can be absent.', 'Correct input.')
  ).

convert(int(X), X) :- !.
convert(expr(/, int(X), int(Y)), X/Y) :- !.
convert(real(X), X) :- !.

/*
replace_by_solutions(Body, Head, Index, Formula, Skolem1, P, Q, NewBody, NewHead) :-
  Discriminant is (P/2)**2 - Q,
  (
    % discriminant is not negative
    Discriminant >= 0
    ->
    % derive the two solutions
    Solution1 is - (P/2) + ((P/2)^2 - Q)^(1/2),
    convert_solution(Solution1, X1),
    Solution2 is - (P/2) - ((P/2)^2 - Q)^(1/2),
    convert_solution(Solution2, X2),
    % create new skolem term Skolem2
    once(retract(skolem_counter(N))),
    N1 is N + 1,
    assert(skolem_counter(N1)),
    name(N, CharList), 								
    name(Skolem2, [115,107|CharList]),
    b_setval(Skolem2, (_Variable, Index)),
    % get object for Skolem1
    support:subterm(object(World, Skolem1, Noun, Class, Unit, Op, Count), (Body, Head)),
    % replace Formula by Solutions and additional object for Skolem2
    support:substitute(Formula, (formula(World, Skolem1, =, X1), formula(World, Skolem2, =, X2), object(World, Skolem2, Noun, Class, Unit, Op, Count)), (Body, Head), (NewBody, NewHead))
  ;
    % discriminant is negative
    Index = [RawIndex],
    RawIndex =.. [Origin, SentenceNumber],
    atomic_list_concat(['A quadratic equation in ', Origin, ' ', SentenceNumber, ' has complex solutions that RACE cannot generate.'], MessageText),  
    add_error_message_once(race, '', MessageText, 'Revise input.'),
    throw(scope)
  ).
*/

replace_by_solutions(OriginalClauses, Head, Index, Formula, Skolem1, P, Q, NewHead) :-
  Discriminant is (P/2)**2 - Q,
  (
    % discriminant is not negative
    Discriminant >= 0
    ->
    % derive the two solutions
    Solution1 is - (P/2) + ((P/2)^2 - Q)^(1/2),
    convert_solution(Solution1, X1),
    Solution2 is - (P/2) - ((P/2)^2 - Q)^(1/2),
    convert_solution(Solution2, X2),
    % get object for Skolem1 from a clause with Index1 from OriginalClauses
    member(satchmo_clause(true, Head1, Index1), OriginalClauses),
    support:subterm(object(World, Skolem1, Noun, Class, Unit, Op, Count), Head1),
    % create new skolem term Skolem2
    once(retract(skolem_counter(N))),
    N1 is N + 1,
    assert(skolem_counter(N1)),
    name(N, CharList), 								
    name(Skolem2, [115,107|CharList]),
    append(Index, Index1, Index2),
    b_setval(Skolem2, (_Variable, Index2)),
    % replace Formula by two formulas for the two solutions and an additional object for Skolem2
    support:substitute(Formula, (formula(World, Skolem1, =, X1), formula(World, Skolem2, =, X2), object(World, Skolem2, Noun, Class, Unit, Op, Count)), Head, NewHead)
  ;
    % discriminant is negative
    Index = [RawIndex],
    RawIndex =.. [Origin, SentenceNumber],
    atomic_list_concat(['A quadratic equation in ', Origin, ' ', SentenceNumber, ' has complex solutions that RACE cannot generate.'], MessageText),  
    add_error_message_once(race, '', MessageText, 'Revise input.'),
    throw(scope)
  ).

convert_solution(Solution, X) :-
  Floor is floor(Solution), 
  (
    Solution =:= Floor
    -> 
    Result = Floor 
  ; 
    Result = Solution
  ),
  (
    integer(Result) 
    ->
    X = int(Result)
  ;
    float(Result) 
    ->
    X = real(Result)
  ).
  
  
%---------------------------------------------------------------------------------------------------------
%
%  supportive predicates in approximately alphabetical order
%
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
%  adjoin heads and bodies of Satchmo clauses 
%
%---------------------------------------------------------------------------------------------------------

adjoin_head(true - Index, _A, true - Index) :- 
  !.

adjoin_head(_A, true - Index, true - Index) :- 
  !.

adjoin_head(fail - Index, fail - Index, fail - Index) :- 
  !.

adjoin_head(fail - _Index, A, A) :- 
  !.

adjoin_head(A, fail - _Index, A) :- 
  !.

adjoin_head((A,B), C, ((A,B) ; C)) :-
  conjunction_of_logical_atoms((A,B), _Result, _Index),
  !.

adjoin_head((A, B), C, ABC) :-
  !,
  % for standard right-associative disjunctions
  adjoin_head(B, C, BC),
  adjoin_head(A, BC, ABC).
/*
  % for left-associative disjunctions as required for complement-splitting in satchmo.pl
  adjoin_head(A, B, AB),
  adjoin_head(AB, C, ABC).
*/

adjoin_head(A, B, (A ; B)).


adjoin_body(true - _Index, A, A) :- 
  !.

adjoin_body(A, true - _Index, A) :- 
  !.

adjoin_body(fail - Index, fail - Index, fail - Index) :- 
  !.

adjoin_body(fail - _Index, A, A) :- 
  !.

adjoin_body(A, fail - _Index, A) :- 
  !.

adjoin_body((A, B), C, ABC) :-
  !,
  adjoin_body(B, C, BC),
  adjoin_body(A, BC, ABC).

adjoin_body(A, B, (A, B)).


%---------------------------------------------------------------------------------------------------------
%
%  conjunction_of_logical_atoms(+ConjunctionInFOLNotation, ?ConjunctionInSatchmoNotation, ?Index) 
%  disjunction_of_logical_atoms(+DisjunctionInFOLNotation, ?DisjunctionInSatchmoNotation, ?Index) 
%
%  conjunctions (disjunctions) of logical atoms in FOL notation - i.e. using the operator '&',  
%  respectively 'v' - are transformed into conjunctions (disjunctions) of logical atoms in the Satchmo 
%  notation - i.e. using the operator ',', respectively ';' 
%  
%  Index is the common index of those logical atoms that are eventually combined in one Satchmo clause
%
%  both predicates can also be used as tests
%
%---------------------------------------------------------------------------------------------------------

conjunction_of_logical_atoms(A & B, (A,NewB), Index) :-
  !,
  logical_atom(A, Index),
  conjunction_of_logical_atoms(B, NewB, Index).

conjunction_of_logical_atoms((A,B), (A,NewB), Index) :-
  !,
  logical_atom(A, Index),
  conjunction_of_logical_atoms(B, NewB, Index).

conjunction_of_logical_atoms(A, A, Index) :-
  logical_atom(A, Index).


disjunction_of_logical_atoms(A v B, (A;NewB), Index) :-
  !,
  logical_atom(A, Index),
  disjunction_of_logical_atoms(B, NewB, Index).

disjunction_of_logical_atoms((A;B), (A;NewB), Index) :-
  !,
  logical_atom(A, Index),
  disjunction_of_logical_atoms(B, NewB, Index).

disjunction_of_logical_atoms(A, A, Index) :-
  logical_atom(A, Index).


%---------------------------------------------------------------------------------------------------------
%
%  disjunction_of_literals(+Literals) 
%
%  Literals is a disjunctions of literals 
%
%  clause set compaction: conjunctions of the form (A,B) and disjunctions of the form (A;B) that were  
%  generated in the step "move negations inside" are also treated as literals
%
%  Index as second argument of logical_atom/2 ensures that only atoms from ACE sentence numbered Index end 
%  up in one Satchmo clause
%
%---------------------------------------------------------------------------------------------------------

disjunction_of_literals(C v D):-
  !,
  disjunction_of_literals(C),
  disjunction_of_literals(D).

disjunction_of_literals(A):-
  literal(A).


literal(-A) :-
  !,
  logical_atom(A, _Index).

literal(A) :-
  logical_atom(A, _Index).


logical_atom((_A,_B), _Index).

logical_atom((_A;_B), _Index).

logical_atom(Atom-Index, Index) :-
  functor(Atom, P, _Arguments),
  \+ logical_symbol(P).


logical_symbol(=>).

logical_symbol(-).

logical_symbol(&).

logical_symbol(v).

logical_symbol(exists).

logical_symbol(forall).


%---------------------------------------------------------------------------------------------------------
%
%  range_restricted(Body, Head, Indices)
%
%  succeeds if all variables of Head occur in Body, otherwise generates warning message
%
%---------------------------------------------------------------------------------------------------------

range_restricted(true, Head, _Indices) :-
  term_variables(Head, []),
  !.

range_restricted(_Body, fail, _Indices) :-
  !.

range_restricted(Body, Head, _Indices) :-
  term_variables(Body, BodyVariables),
  term_variables(Head, HeadVariables),
  variable_subtract(HeadVariables, BodyVariables, []),
  !.

% not range restricted
range_restricted(_Body, _Head, Indices) :-
  Indices = [Index],
  Index =.. [Origin, SentenceNumber],
  atomic_list_concat(['A clause derived from ', Origin, ' ', SentenceNumber, ' violates range restriction and is skipped.'], MessageText),  
  add_warning_message_once(race, '', MessageText, 'Check input.'),
  fail.


%---------------------------------------------------------------------------------------------------------
%
%  scrub_indices_from_body(Body, ScrubbedBody, IndicesIn, IndicesOut)
%  scrub_indices_from_head(Head, ScrubbedHead, IndicesIn, IndicesOut)
%
%  both predicates remove indices from all atoms in Body, respectively Head, and return ScrubbedBody,
%  respectively ScrubbedHead
%
%  removed indices are collected in the accumulator pair IndicesIn/IndicesOut
%
%---------------------------------------------------------------------------------------------------------

scrub_indices_from_body((Body, RestBody), (ScrubbedBody, ScrubbedRestBody), IndicesIn, IndicesOut) :-
  !,
  scrub_indices_from_body(Body, ScrubbedBody, IndicesIn, IndicesIntermediate),
  scrub_indices_from_body(RestBody, ScrubbedRestBody, IndicesIntermediate, IndicesOut).

scrub_indices_from_body(Body, ScrubbedBody, IndicesIn, [Index|IndicesIn]) :-
  (
    Body = Atom - Index
    ->
    ScrubbedBody = Atom
  ;
    disjunction_of_logical_atoms(Body, _BodyInSatchmoNotation, Index)
    ->
    scrub_indices_from_head(Body, ScrubbedBody, _IndexIn, _IndexOut)
  ).
  

scrub_indices_from_head((Head ; RestHead), (ScrubbedHead ; ScrubbedRestHead), IndicesIn, IndicesOut) :-
  !,
  scrub_indices_from_head(Head, ScrubbedHead, IndicesIn, IndicesIntermediate),
  scrub_indices_from_head(RestHead, ScrubbedRestHead, IndicesIntermediate, IndicesOut).

scrub_indices_from_head(Head, ScrubbedHead, IndicesIn, [Index|IndicesIn]) :-
  (
    Head = Atom - Index
    ->
    ScrubbedHead = Atom
  ;
    conjunction_of_logical_atoms(Head, _HeadInSatchmoNotation, Index)
    ->
    scrub_indices_from_body(Head, ScrubbedHead, _IndexIn, _IndexOut)
  ).  


%---------------------------------------------------------------------------------------------------------
%
%  Work Place
%
%---------------------------------------------------------------------------------------------------------

/*

convert_one_conjunction(satchmo_clause(Body, Head, Indices), ClausesIn, ClausesOut) :-
  (
    % clause is range restricted
    range_restricted(Body, Head, Indices)
    ->
    interpret_copula1(Body, Head, NewBody, NewHead),
    ClausesOut = [satchmo_clause(NewBody, NewHead, Indices)| ClausesIn]
    ClausesOut = [satchmo_clause(Body, Head, Indices)| ClausesIn]
  ;
    % clause is not range restricted 
    ClausesOut = ClausesIn
  ).

interpret_copula1(Body, Head, NewBody, NewHead) :-
  (
    % A man is a human.
    % satchmo_clause(true, (object(sk1, sk2, man, countable, na, eq, 1), object(sk1, sk3, human, countable, na, eq, 1), predicate(sk1, sk4, be, sk2, sk3))
    Body = true,
    support:subterm(predicate(World, A, be, B, C), Head),
    support:subterm(object(World, Referent, _Noun, _Count, na, _EQ, _Num), Head),
    Referent == C
    ->
    substitute(predicate(World, A, be, B, C), predicate(World, A, be_NP, B, C), Head, NewHead),
    NewBody = Body
  ;
    % No  man is a human.
    % Every  man is not a human.
    % satchmo_clause((object(sk1, _G656, man, countable, na, eq, 1), object(sk1, _G2346, human, countable, na, eq, 1), predicate(sk1, _G2041, be, _G656, _G2346)), fail,
    Head = fail,
    support:subterm(predicate(World, A, be, B, C), Body),
    support:subterm(object(World, Referent1, Noun1, countable, na, eq, 1), Body),
    Referent1 == B,
    support:subterm(object(World, Referent2, Noun2, countable, na, eq, 1), Body),
    Referent2 == C
    ->
    substitute(object(World, Referent1, Noun1, countable, na, eq, 1), object(World, Referent1, Noun1, countable, na, eq, Number1), Body, IntermediateBody1),
    substitute(object(World, Referent2, Noun2, countable, na, eq, 1), object(World, Referent2, Noun2, countable, na, eq, Number2), IntermediateBody1, IntermediateBody2),
    substitute(predicate(World, A, be, B, C), predicate(World, A, be_NP, B, C), IntermediateBody2, NewBody),
    NewHead = Head
  ;
    % A  man is not a human.
    % satchmo_clause((object(sk1, _G2332, human, countable, na, eq, 1), predicate(sk1, _G2013, be, sk2, _G2332)), fail 
    % satchmo_clause(true, object(sk1, sk2, man, countable, na, eq, 1)
    Head = fail,
    support:subterm(predicate(World, A, be, B, C), Body),
    support:subterm(object(World, Referent, _Noun, _Count, na, _EQ, _Num), Body),
    Referent == C
    ->
    substitute(predicate(World, A, be, B, C), predicate(World, A, be_NP, B, C), Body, NewBody),
    NewHead = Head
  ;
    % Every man is a human.
    % No  man is not a human.
    % satchmo_clause(object(sk1, _G692, man, countable, na, eq, 1), (object(sk1, sk2(_G692), human, countable, na, eq, 1), predicate(sk1, sk3(_G692), be, _G692, sk2(_G692)))
    support:subterm(predicate(World, A, be, B, C), Head),
    support:subterm(object(World, Referent1, Noun1, countable, na, eq, 1), Body),
    Referent1 == B,
    support:subterm(object(World, Referent2, Noun2, countable, na, eq, 1), Head),
    Referent2 == C
    ->
%%%    substitute(object(World, Referent1, Noun1, countable, na, eq, 1), object(World, Referent1, Noun1, countable, na, eq, Number), Body, NewBody),
%%%    substitute(object(World, Referent2, Noun2, countable, na, eq, 1), object(World, Referent2, Noun2, countable, na, eq, Number), Head, IntermediateHead),
%%%    substitute(predicate(World, A, be, B, C), predicate(World, A, be_NP, B, C), IntermediateHead, NewHead)
    substitute(object(World, Referent1, Noun1, countable, na, eq, 1), object(World, Referent, Noun1, countable, na, eq, Number), Body, NewBody),
    substitute(object(World, Referent2, Noun2, countable, na, eq, 1), object(World, Referent, Noun2, countable, na, eq, Number), Head, IntermediateHead),
    substitute(predicate(World, A, be, B, C), predicate(World, A, be_NP, Referent, Referent), IntermediateHead, NewHead)
  ;
    % Every  professor is a man or is a woman.
    % satchmo_clause(object(sk1, _G148, professor, countable, na, eq, 1), (object(sk1, sk10(_G148), man, countable, na, eq, 1), predicate(sk1, sk11(_G148), be, _G148, sk10(_G148)) 
    %										                               ; 
    %										                               object(sk1, sk12(_G148), woman, countable, na, eq, 1), predicate(sk1, sk13(_G148), be, _G148, sk12(_G148)))
    Head = (Head 1 ; Head 2)                                                                       
    ->
    interpret_copula1(Body, Head1, NewBody, NewHead1),
    interpret_copula1(Body, Head2, NewBody, NewHead2),
    NewHead = (NewHead 1 ; NewHead 2)
  ;
    % do nothing
    NewBody = Body,
    NewHead = Head
  ).

%---------------------------------------------------------------------------------------------------------
%
%  tautological(Body, Head, Indices)
%
%  clause Body -> Head is tautological if Body and Head contain unifying atoms
%  
%  warning mesages are generated for tautological clauses
%
%---------------------------------------------------------------------------------------------------------

tautological(Body, Head, Indices) :-
  % clause is tautological if Body and Head contain unifying atoms 
  % (e.g. a -> a or a -> (a ; b) or (a,b) -> a)
  conjunct(Conjunct, Body),
  disjunct(Disjunct, Head),
  \+ \+ Conjunct = Disjunct,
  Indices = [Index],
  Index =.. [Origin, SentenceNumber],
  atomic_list_concat(['Tautological ', Origin, ' ', SentenceNumber, ' is skipped.'], MessageText),
  add_warning_message_once(race, '', MessageText, 'Check input.').


conjunct(X,X) :-
  \+ X = (_ , _).

conjunct(X, (X , _Rest)).

conjunct(X, (_First , Rest)) :-
  conjunct(X, Rest).
  

disjunct(X,X) :-
  \+ X = (_ ; _).

disjunct(X, (X ; _Rest)).

disjunct(X, (_First ; Rest)) :-
  disjunct(X, Rest).
*/

%---------------------------------------------------------------------------------------------------------
