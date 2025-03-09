%---------------------------------------------------------------------------------------------------------
%
%  Extended Tableaux-Based Theorem Prover (Model Generator) for Range-Restricted First-Order Clauses
% 
%  N. E. Fuchs
%  University of Zurich
%
%  15 July 2022
%
%---------------------------------------------------------------------------------------------------------
%
%  Technical Details
%
%  based on the original Satchmo (R. Manthey & F. Bry, ECRC München, 1988) and on a fair version of Satchmo 
%  (F. Bry & A. Yahya, Universität München, 1996) 
%
%  essential modifications: 
%    while all previous versions of Satchmo search for a minimal model and immediately stop once they detect
%    that the clause set is inconsistent, this version finds all inconsistencies of an inconsistent set and 
%    all minimal models for a consistent one 
%
%    handling of arithmetic, aggregation and non-monotonic reasoning
%
%  satchmo(Clauses, Model, Inconsistencies) returns for a set of range-restricted clauses either a set of models
%  or a set of sets of inconsistent clauses
%
%  clauses have the form satchmo_clause(Body, Head, Indices) where Body implies Head, and the list Indices 
%  contains the sorted indices of the atoms of Body and Head (cf. fol_to_clauses/1)
%
%  facts are expressed as satchmo_clause(true, Head, Indices)
%
%  negated clauses are written as satchmo_clause(Body, fail, Indices) 
%
%  clause set compaction:
%
%    Body has the form 'B1, B2, ..., Bn' where Bi has the form 'Bi1 ; B12 ; ... ; Bin' and Bik is a logical 
%    atom; ',' stands for logical conjunction, ';' for logical disjunction
%
%    Head has the form 'H1 ; H2 ; ... ; Hn' where Hi has the form 'Hi1, H12, ... , Hin' and Hik is a logical 
%    atom; ',' stands for logical conjunction, ';' for logical disjunction 
%
%  all variables occurring in Body and Head are implicitly universally quantified 
%
%  logical atoms are either user-defined predicates derived from first-order formulas, or built-in or 
%  imported Prolog predicates that are immediately executed
%
%  all logical atoms have an index that occurs in the list Indices
% 
%  indices are, for instance, axiom(3), theorem(6), or fol_axiom(7) that shows from which ACE sentence, 
%  respectively auxiliary FOL axiom, the atom was derived, and whether it belongs to the axioms, to 
%  the theorems, or to the auxiliary FOL axioms
%
%  clauses are range-restricted, i.e. all variables occurring in the head of a clause occur in the body
%  of the clause; as a consequence facts are ground and unification does not need an occur check
%
%  branches of the tableau are expanded beyond the occurrence of a failing built-in or imported Prolog
%  predicate - indicating closure of the respective branch - to find all inconsistent minimal subsets of 
%  an inconsistent set of clauses
%
%  if the set of clauses is unsatisfiable then the structure closed_branch(Indices) - found in the Prolog 
%  data base - contains the list Indices of a subset of unsatisfiable clauses; for each unsatisfiable
%  subset there is one instance of closed_branch/1 
%
%  if the set of clauses is satisfiable then the structure model(Model) - found in the Prolog data base -
%  returns in the list Model the elements of the Herbrand model generated; if the set of clauses is 
%  unsatisfiable then the model is empty
%
%---------------------------------------------------------------------------------------------------------
%
%  To do
%
%  why call spurious_closed_branch?
%
%  asserted atoms belonging to an already processed branch are individually blocked in prove_body_goal/4;  
%  would it be more efficient to retract all asserted atoms of one branch once the branch is completely 
%  processed?; this had the consequence that atoms that are asserted before a disjunction - e.g those
%  coming from clauses with body "true" - and that need to be available in all branches would have to 
%  be treated specially
%
%  check clause compaction here and in fol_to_clauses/2; is_candidate would need to be adapted
%
%  complement splitting? (check for consistent left/right association of disjunctions etc.)
%
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
% declarations
%
%---------------------------------------------------------------------------------------------------------

% module definition and exported predicates
:- module(satchmo, [satchmo/3]).

% operators
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

% local dynamic predicates
:- dynamic(closed_branch/1).
:- dynamic(disjunctive_branches/1).
:- dynamic(branch/1).


% RACE modules
:- use_module(race_error_logger).
:- use_module(auxiliary_axioms). 
:- use_module(support).


%---------------------------------------------------------------------------------------------------------
%
% satchmo(+Clauses, -Model, -Inconsistencies)
%
%---------------------------------------------------------------------------------------------------------

satchmo(Clauses, Model, Inconsistencies) :-
  (
    % no clauses
    (var(Clauses) ; Clauses = [])
    ->
    add_error_message(race, '', 'No clauses found.', '')
  ;
    %%%nl, write('Clauses: '), write(Clauses),
    clean_up_from_previous_run,
    % make clauses globally available
    user:assert(clauses(Clauses)),
    % TimeOutLimit is number of clauses times 20 ms with a lower limit of 10 s and an upper limit of 20 s
    length(Clauses, NumberOfClauses),
    TimeOutLimitRaw is 0.02 * NumberOfClauses,
    (
      TimeOutLimitRaw < 10.0 
      -> 
      TimeOutLimit = 10.0
    ; 
      TimeOutLimitRaw >= 10.0,
      TimeOutLimitRaw < 20.0
      ->
      TimeOutLimit = TimeOutLimitRaw
    ;
      TimeOutLimit = 20.0
    ),
    % for testing without time-out limit activate next line and deactivate the following line
    %%%satisfiable(Clauses, Model, Inconsistencies)
    catch(call_with_time_limit(TimeOutLimit, satisfiable(Clauses, Model, Inconsistencies)), time_limit_exceeded, reaction_on_time_out(Inconsistencies))
  ).

reaction_on_time_out(Inconsistencies) :-
  collect_indices_of_all_inconsistent_clauses(Inconsistencies),
  (
    \+ Inconsistencies = []
    -> 
    add_warning_message(timelimit, '', 'RACE time limit reached.', 'Some - but possibly not all - inconsistencies/proofs/answers were found before time-out.')
  ;
    % Inconsistencies = []
    nb_getval(global_parameters, Parameters),
    (
      % consistency checking
      memberchk(check_consistency, Parameters)
      ->
      add_warning_message(timelimit, '', 'RACE time limit reached.', 'No inconsistency was detected before time-out. Possibly undecidable case.')
    ;
      % proof or query answering
      add_warning_message(timelimit, '', 'RACE time limit reached.', 'No proofs/answers were found before time-out. Possibly undecidable case.')
    )
  ).

%---------------------------------------------------------------------------------------------------------
%
% satisfiable(+Clauses, -Model, -Inconsistencies)
%
%---------------------------------------------------------------------------------------------------------

satisfiable(Clauses,  Model, Inconsistencies) :-
  % process arithmetic formulas of all fact clauses satchmo_clause(true, Head, Indices) 
  % to detect inconsistent formulas and to identify not fully instantiated formulas since all formulas of 
  % fact clauses must be processed together
  % problem with this approach: formulas of the form 'A is 1 or is 2.' are incorrectly found arithmetically 
  % inconsistent; must possibly be replaced by an equivalent construct like 'V=0. If V=0 then A=1 or A=2.'
  % or by 'A number is 1. A number is 2.'
  process_formulas_of_fact_clauses(Clauses),
  !,
  % if there are clauses with disjunctive heads then the tableau derived from them has several branches 
  % determine the model and the inconsistencies for all branches of the tableau
  findall(
    (OneBranchModel, OneBranchInconsistencies), 
    % determine for each branch the model using only clauses whose head is not "fail"
    % start find_model_of_one_branch/4 with argument RecentlyAdded = true to process fact clauses first
    (find_model_of_one_branch(Clauses, [true], [], OneBranchModel),
    % determine for each branch the inconsistencies using only clauses whose head is "fail"
    findall(Indices, find_inconsistencies_of_one_branch(Clauses, Indices), OneBranchInconsistencies)), ResultsForAllBranches),
  %%%nl, write('ResultsForAllBranches '), write(ResultsForAllBranches),
  % analyse the results for the complete tableau ...
  % ... collect the models of all open branches ...
  findall(OneBranchModel, member((OneBranchModel, []), ResultsForAllBranches), Model),
  % ... collect the indices of all inconsistent clauses
  collect_indices_of_all_inconsistent_clauses(Inconsistencies).

/*
% simplification: no disjunctive heads
satisfiable(Clauses,  Model, Inconsistencies) :-
  % process arithmetic formulas of all fact clauses satchmo_clause(true, Head, Indices) 
  process_formulas_of_fact_clauses(Clauses),
  !,
  % determine the model and the inconsistencies for the one branch of the tableau
  find_model_of_one_branch(Clauses, [true], [], Model),
  findall(Indices, find_inconsistencies_of_one_branch(Clauses, Indices), _OneBranchInconsistencies), 
  collect_indices_of_all_inconsistent_clauses(Inconsistencies).
*/

%---------------------------------------------------------------------------------------------------------
%
% find_model_of_one_branch(+Clauses, +RecentlyAdded, +ModelIn, -ModelOut) 
%
%---------------------------------------------------------------------------------------------------------

find_model_of_one_branch(Clauses, RecentlyAdded, ModelIn, ModelOut) :-
  %%%nl, write('ModelIn: '), write(ModelIn),
  % 20 April 2017: replaced in the next line setof/3 by bagof/3 to leave the order of elements of Clauses unchanged in ViolatedInstances
  bagof(ViolatedInstance, find_violated_instance(Clauses, RecentlyAdded, ViolatedInstance)^find_violated_instance(Clauses, RecentlyAdded, ViolatedInstance), ViolatedInstances),
  !,
  %%%nl, write('Violated Instances: '), write(ViolatedInstances),
  % try to satisfy violated instances
  satisfy_all(ViolatedInstances, ModelIn, ModelIntermediate),
  % get elements recently added to the model
  subtract(ModelIntermediate, ModelIn, NewRecentlyAdded),
  %%%nl, write('Recently added: '), write(NewRecentlyAdded),
  % continue forward chaining  
  find_model_of_one_branch(Clauses, NewRecentlyAdded, ModelIntermediate, ModelOut).

find_model_of_one_branch(_Clauses, _RecentlyAdded, Model, Model).


%---------------------------------------------------------------------------------------------------------
%
%  find_violated_instance(+Clauses, +RecentlyAdded, -violated_instance(Head, Indices))
%
%  Head – that is not "fail" – occurs in the clause satchmo_clause(Body, Head, Index) whose Body could be  
%  proved using the predicates indexed by Indices while Head could not be proved
%  
%---------------------------------------------------------------------------------------------------------

find_violated_instance(Clauses, RecentlyAdded, violated_instance(Head, Indices)) :-
  % select clauses whose Head is not "fail" and ...
  member(satchmo_clause(Body, Head, Index), Clauses),
  \+ Head = fail, 
  % ... whose body is "true" or contains at least one of the atoms recently added to the Prolog data base
  \+ \+ is_candidate(Body, RecentlyAdded),
  %%%nl, write('Is candidate: '), write(Body), nl, write('Recently Added: '), write(RecentlyAdded),
  prove_body(Body, Index, [], Indices),
  % if Body contains a naf/1 condition then not all Head variables will necessarily be instantiated by unification with Body variables, thus ...
  (
    subterm(naf(NAFList), Body),
    \+ term_variables(NAFList, [])
    ->
    % ... replace any remaining uninstantiated Head variables by constants
    numbervars(Head, 1, _)
  ; 
    true
  ),
  \+ prove_head(Head, Index), 
  % Head fails: collect information concerning potential inconsistencies
  (
    % Head contains a disjunction of conjunctions of atoms
    support:subterm((Disjunct ; Disjuncts), Head),
    convert_disjunction_into_list_of_disjuncts((Disjunct ; Disjuncts), ListofDisjuncts)
    ->
    (
      % collect all disjunctives branches in the order they are encountered
      disjunctive_branches(DisjunctiveBranches),
      % new disjunctive branch
      \+ memberchk(ListofDisjuncts, DisjunctiveBranches) 
      ->
      %%%nl, write('Retracting: '), write(disjunctive_branches(DisjunctiveBranches)),
      once(retract(disjunctive_branches(DisjunctiveBranches))),
      %%%nl, write('Asserting: '), write(disjunctive_branches([ListofDisjuncts|DisjunctiveBranches])),
      assert(disjunctive_branches([ListofDisjuncts|DisjunctiveBranches]))
    ;
      % no new disjunctive branch
      true
    )
  ;
    % Head is an atom or a conjunction of atoms
    /*
    %%% activate the following lines to get a trace of the axioms and theorems used for the proof Axioms |- Theorems
    user:axioms_theorems(Axioms, Theorems),
    (
      Index = [axiom(I)],
      (
        I = 0
        ->
        true
      ;
        nth1(I, Axioms, Axiom),
        nl, write('Axiom used in proof:   '), write(Axiom)
      )
    ;
      Index = [theorem(I)],
      (
        I = 0
        ->
        true
      ;
        nth1(I, Theorems, Theorem),
        nl, write('Theorem used in proof: '), write(Theorem)
      )
    ),
    %%% also activate the lines 338 ...
    %%% also activate the respective lines 2482 ... in auxiliary_axioms
    */
    true
  ).


%---------------------------------------------------------------------------------------------------------
%
%  find_inconsistencies_of_one_branch(+Clauses, -Indices)
%
%  select all clauses with the head fail and try to prove their Body and assimilate the Indices collected
%  during the proof as closed branch
%  
%---------------------------------------------------------------------------------------------------------

find_inconsistencies_of_one_branch(Clauses, Indices) :-
  % select clauses whose Head is "fail"
  member(satchmo_clause(Body, fail, Index), Clauses),
  prove_body(Body, Index, [], Indices),
  /*
  %%% activate the following lines to get a trace of the axioms and theorems used for the proof Axioms |- Theorems
  user:axioms_theorems(Axioms, Theorems),
  (
    Index = [axiom(I)],
    (
      I = 0
      ->
	  true
    ;
	  nth1(I, Axioms, Axiom),
	  nl, write('Axiom used in proof:   '), write(Axiom)
    )
  ;
    Index = [theorem(I)],
    (
	  I = 0
	  ->
	  true
    ;
	  nth1(I, Theorems, Theorem),
	  nl, write('Theorem used in proof: '), write(Theorem)
    )
  ),
  %%% also activate the lines 295 ..
  %%% also activate the respective lines 2482 ... in auxiliary_axioms
  */
  % Head fails per default
  % assimilate indices of closed branch
  assimilate_closed_branch(Indices).


%---------------------------------------------------------------------------------------------------------
%
%  prove_body(+Body, +IndexOfBody, +IndicesIn, -IndicesOut)
%
%  check that the goals of Body can be proved either from the Prolog data base, as built-in predicates, or
%  as predicates exported from auxiliary_axioms.pl 
%
%  indices IndexOfBody and of matching goals are collected by the accumulator pair IndicesIn/IndicesOut
%
%---------------------------------------------------------------------------------------------------------

prove_body(Body, IndexOfBody, IndicesIn, IndicesOut) :-
  % process first body elements that are not formulas to instantiate variables then ...
  % note: formulas are skipped in prove_body_goal/4
  prove_body_without_formulas(Body, IndexOfBody, IndicesIn, IndicesOfNonFormulas),
  % ... process arithmetic formulas of Body if Body is not 'true'
  (
    Body = true
    ->
    IndicesOfFormulas = []
  ;
    process_formulas_of_body(Body, IndexOfBody, IndicesOfFormulas)
  ),
  append([IndicesOfNonFormulas, IndicesOfFormulas], RawIndices),
  flatten(RawIndices, FlattenedRawIndices),
  sort(FlattenedRawIndices, IndicesOut).

prove_body_without_formulas(Body, IndexOfBody, IndicesIn, IndicesOut) :-  
  (
    % Body is a conjunction of atoms
    Body = (Goal, Goals)
    ->
%%%%%% 26 Feb 2021: deactivated because conflicts with companion of Prolog axiom w8 that expects queries at the beginning of Body
%%%%%% 26 May 2022: reactivated since restricting to the case "What does ... do?" the conflict disappears
    (
      % move query to the end of Body for the case of "What does ... do?"
      subterm(predicate(World, _RefPredicate, do, _Agent, RefQuery), Body),
      subterm(query(World, RefQuery, what), Body)
      ->
      move_queries(Body,(NewGoal, NewGoals))
    ;
      NewGoal = Goal, 
      NewGoals = Goals
    ),
%%%%%%
    prove_body_goal(NewGoal, IndexOfBody, IndicesIn, IndicesIntermediate),
    prove_body_without_formulas(NewGoals, IndexOfBody, IndicesIntermediate, IndicesOut)
  ;
    % Body is an atom
    prove_body_goal(Body, IndexOfBody, IndicesIn, IndicesOut)
  ).

move_queries(Body, NewBody) :-
  conjunction_to_list(Body, BodyAsList),
  move_queries1(BodyAsList, NewBodyAsList),
  list_to_conjunction(NewBodyAsList, NewBody).
 
move_queries1([], []).

move_queries1(BodyAsList, NewBodyAsList) :- 
  (
    select(query(World, Referent, QueryWord), BodyAsList, RestBodyAsList)
    ->
    move_queries1(RestBodyAsList, IntermediateBodyAsList),
    append(IntermediateBodyAsList, [query(World, Referent, QueryWord)], NewBodyAsList)
  ;
    NewBodyAsList = BodyAsList
  ).


/*
prove_body_without_formulas(Body, IndexOfBody, IndicesIn, IndicesOut) :-  
  (
    % Body is a conjunction of atoms
    Body = (Goal, Goals)
    ->
    (
      % Goal is a query
      % delay its proof until its referent is instantiated by other goals to eliminate 
      % possible backtracking in the auxiliary axioms for query words
      Goal = query(_World, _Referent, _QueryWord)
      ->
      prove_body_without_formulas(Goals, IndexOfBody, IndicesIn, IndicesIntermediate),
      prove_body_goal(Goal, IndexOfBody, IndicesIntermediate, IndicesOut)
    ;
      % Goal is not a query
      prove_body_goal(Goal, IndexOfBody, IndicesIn, IndicesIntermediate),
      prove_body_without_formulas(Goals, IndexOfBody, IndicesIntermediate, IndicesOut)
    )
  ;
    % Body is an atom
    prove_body_goal(Body, IndexOfBody, IndicesIn, IndicesOut)
  ).
*/

  
/* RACE does not use clause compaction
prove_body_goal((Goal ; Goals), IndexOfGoal, IndicesIn, IndicesOut) :-
  % (Goal ; Goals) is a disjunction of atoms
  !,
  (
    prove_body_goal(Goal, IndexOfGoal, IndicesIn, IndicesOut)
  ;
    prove_body_goal(Goals, IndexOfGoal, IndicesIn, IndicesOut)
  ).
*/

 prove_body_goal(Goal, IndexOfGoal, IndicesIn, IndicesOut) :-
  % Goal is an atom
  (
    % Goal is the built-in predicate "true"
    Goal = true
    ->
    append(IndexOfGoal, IndicesIn, IndicesIntermediate)
  ;
    % Goal is a formula
    % just collect indices
    % do not allow for backtracking
    Goal = formula(_World, _LHS, _Operator, _RHS)
    ->
    append(IndexOfGoal, IndicesIn, IndicesIntermediate)
  ;
    % Goal is a list of weakly negated user-defined predicates (negation-as-failure)
    % allow for backtracking
    Goal = naf(NAFList)
    -> 
    (
      % NAFList succeeds since every individual goal exists in the Prolog database, thus naf(NAFList) fails
      list_to_conjunction(NAFList, NAFListAsConjunction),
      prove_body(NAFListAsConjunction, IndexOfGoal, IndicesIn, IndicesOut)
      ->
      fail
    ;
      % NAFList fails since at least one individual goal does not exist in the Prolog database, thus naf(NAFList) succeeds
      % keep the auxiliary axioms c1c and c11 out of the way that would interfere with the correct solution
      \+ member(prolog_axiom(c1c), IndicesIn), 
      \+ member(prolog_axiom(c11), IndicesIn),
      append(IndexOfGoal, IndicesIn, IndicesIntermediate)
    )
  ;
    % Goal is a user-defined predicate previously added to the Prolog database
    % allow for backtracking to find multiple solutions, e.g.
    % 'There is a red apple. There is a green apple.'|- 'There is an apple.'
    exists_asserted_atom(Goal, IndicesOfGoalInPrologDataBase),
    % check that we are in the correct branch or in a non-branching situation
    (
      memberchk(disjunct(_), IndicesOfGoalInPrologDataBase)
      ->
      forall(member(disjunct(Branch), IndicesOfGoalInPrologDataBase), branch(Branch))
    ;
      true
    ),
    append([IndexOfGoal, IndicesOfGoalInPrologDataBase, IndicesIn], IndicesIntermediate)
  ;
    % Goal is a Prolog axiom exported by auxiliary_axioms.pl 
    % allow for backtracking to find multiple solutions, e.g.
    % 'Three boys eat a large pizza. Four boys eat a small pizza.'|- 'Two boys eat a pizza.' 
    % initialise IndicesSoFar to IndicesIn to prevent in auxiliary_axioms the combination of incompatible axioms
    predicate_property(prolog_axiom(Goal, _IndicesSoFar, _Indices), imported_from(auxiliary_axioms)), 
    auxiliary_axioms:prolog_axiom(Goal, IndicesIn, IndicesOfAxiom),
    %%%nl, write('BodyGoal '), write(Goal), write(' proved by auxiliary axiom '), write(IndicesOfAxiom),
    append([IndexOfGoal, IndicesOfAxiom, IndicesIn], IndicesIntermediate)
  ),
  flatten(IndicesIntermediate, FlattenedIndicesIntermediate),
  sort(FlattenedIndicesIntermediate, IndicesOut).


%---------------------------------------------------------------------------------------------------------
%
%  prove_head(+Head, +IndexOfHead)
%
%  check that the goals of Head can be proved either from the Prolog data base, as built-in predicates,  
%  or as predicates exported from auxiliary_axioms.pl 
%
%---------------------------------------------------------------------------------------------------------

prove_head((Disjunct ; Disjuncts), IndexOfHead) :-
  % right-associative disjunction of atoms
  !,
  (
    prove_head(Disjunct, IndexOfHead)
  ;
    prove_head(Disjuncts, IndexOfHead)
  ).

prove_head(Head, IndexOfHead) :-
  % process first head elements that are not formulas to instantiate variables then ...
  % note: formulas are skipped in prove_head_goal/2
  prove_head_without_formulas(Head, IndexOfHead),
  % ... process arithmetic formulas of Head if Head is not 'fail' and ...
  % ... if pertinent body is not 'true' (this case is processed by process_formulas_of_fact_clauses/1)
  (
    Head = fail
    ->
    true
  ;
    user:clauses(Clauses),
    member(satchmo_clause(true, Head, IndexOfHead), Clauses)
    ->
    true
  ;
    process_formulas_of_head(Head, IndexOfHead)
  ).


prove_head_without_formulas(Head, IndexOfHead) :-  
  (
    % Head is a conjunction of atoms
    Head = (Goal, Goals)
    ->
    prove_head_goal(Goal, IndexOfHead),
    prove_head_without_formulas(Goals, IndexOfHead)
  ;
    % Head is an atom
    prove_head_goal(Head, IndexOfHead)
  ).

  
prove_head_goal(Goal, _IndexOfHead) :-
  (
/*
    Goal = formula(_World, _LHS, _Operator, _RHS)
    ->
    true
  ;
*/
    % Goal is a user-defined predicate previously asserted to the Prolog data base
    user:call(Goal)
    -> 
    true
  ).


%---------------------------------------------------------------------------------------------------------
%
%  satisfy_all(+ViolatedInstance, +ModelIn, -ModelOut)
%
%  ViolatedInstance is a list of terms violated_instance(Head,Indices) where Head occurs in the clause 
%  satchmo_clause(Body, Head, Index) whose Body could be proved using the predicates indexed by Indices 
%  while Head could not be proved
%
%  satisfy_all satisfies each violated instance by proving Head in one of three ways:
%    – Head has already been asserted to the Prolog data base, or 
%    – Head is a succeeding Prolog predicate, or 
%    – by assuming Head and Indices
%
%  satisfy_all/3 fails if Head is a failing built-in Prolog predicate, specifically if Head = fail
%  
%---------------------------------------------------------------------------------------------------------

satisfy_all([], Model, Model).

satisfy_all([ViolatedInstance|ViolatedInstances], ModelIn, ModelOut) :-
  satisfy(ViolatedInstance, ModelIn, ModelIntermediate),
  satisfy_all(ViolatedInstances, ModelIntermediate, ModelOut).

/*
% Artificial recursive problem: 
% A number is 10. If there is a number N and N>4 then there is a number  N1 and N1 = N - 1. |- A number is 4.
satisfy(violated_instance((Conjunct, Conjuncts),Indices), ModelIn, ModelOut) :-
  % head of violated instance is a conjunction of atoms
  % head failed because at least one conjunct failed while other conjuncts may have succeeded
  % failing and succeeding atoms are treated accordingly in the 3rd clause of satisfy/1
  !,
  (
    % there is a formula with an expression whose left side is not an atomic skolem and whose first argument is an atomic skolem
    % example: formula(World, sk4(sk2), =, expr(+, sk2, int(1))) derived from the 'then' part of the second axiom of ...
    % A number is 1. If there is a number N then there is a number  N1 and N1 = N + 1.|- A number is 3.
    subterm(formula(World,LHS,=,expr(Operator,FirstArgument,SecondArgument)), (Conjunct, Conjuncts)),
    \+ atom(LHS),
    atom(FirstArgument)
    %%%,nl, write('(Conjunct, Conjuncts):  '), write((Conjunct, Conjuncts))
    ->
    % evaluate expression
    convert(expr(Operator,FirstArgument,SecondArgument), Expression, _, _),
    FullResult is Expression,
    % get integer part
    floor(FullResult, Result),
    % store new value for LHS taking into account that the first argument of b_setval/2 must be an atom
    % examples: sk4(sk2) -> 'sk4(sk2)', sk4('sk4(sk2)') -> 'sk4(sk4(sk2))'
    LHS =.. [Functor, Argument], atom(Argument), atom_to_term(Argument, Term, _), NewLHS =.. [Functor, Term], term_to_atom(NewLHS, NewLHSAsAtom),
    b_setval(NewLHSAsAtom, (Result, Indices)),
    % substitute the right hand side of the formula by the result
    substitute(expr(Operator,FirstArgument,SecondArgument), int(Result), (Conjunct, Conjuncts), (IntermediateConjunct, IntermediateConjuncts)),
    % substitute skolem: LHS -> NewLHSAsAtom
    substitute(LHS, NewLHSAsAtom, (IntermediateConjunct, IntermediateConjuncts), (NewConjunct, NewConjuncts))
    %%%,nl, write('(NewConjunct, NewConjuncts):  '), write((NewConjunct, NewConjuncts))
  ;
     % there is no such formula
     NewConjunct = Conjunct,
     NewConjuncts = Conjuncts
  ),
  satisfy(violated_instance(NewConjunct,Indices), ModelIn, ModelIntermediate),
  satisfy(violated_instance(NewConjuncts,Indices), ModelIntermediate, ModelOut).  
*/

satisfy(violated_instance((Conjunct, Conjuncts),Indices), ModelIn, ModelOut) :-
  % head of violated instance is a conjunction of atoms
  % head failed because at least one conjunct failed while other conjuncts may have succeeded
  % failing and succeeding atoms are treated accordingly in the 3rd clause of satisfy/1
  !,
  satisfy(violated_instance(Conjunct,Indices), ModelIn, ModelIntermediate),
  satisfy(violated_instance(Conjuncts,Indices), ModelIntermediate, ModelOut).  

% right-associative disjunction
satisfy(violated_instance((Disjunct ; Disjuncts), Indices), ModelIn, ModelOut) :- 
  % head of violated instance is a disjunction of conjunctions of atoms
  % disjunction is parsed as a right-associative operator
  % each disjunct in turn is added to Indices to distinguish the branches of the disjunction
  !,
  (
    % label active branch and ...
    assert(branch(Disjunct)),
    %%%nl, write('Asserting: '), write(branch(Disjunct)), 
    % ... investigate it
    once(satisfy(violated_instance(Disjunct,[disjunct(Disjunct)|Indices]), ModelIn, ModelOut))
  ; 
    % retract label of active branch and ...
    retract(branch(Disjunct)),
    %%%nl, write('Retracting: '), write(branch(Disjunct)),
    % ... check rest of disjunction
    (
      % if at least two disjuncts remain then ...
      Disjuncts = (_ ; _)
      ->
      % ... recurse
      satisfy(violated_instance(Disjuncts,Indices), ModelIn, ModelOut)
    ;
      % if one disjunct remains then label it and ...
      assert(branch(Disjuncts)),
      %%%nl, write('Asserting last disjunct: '), write(branch(Disjuncts)),
      % ... investigate it
      once(satisfy(violated_instance(Disjuncts,[disjunct(Disjuncts)|Indices]), ModelIn, ModelOut))
    )
  ).  

/* 
% left-associative disjunction
satisfy(violated_instance((Disjuncts ; Disjunct),Indices), ModelIn, ModelOut) :- 
  % head of violated instance is a disjunction of conjunctions of atoms
  % disjunction is parsed as a left-associative operator
  % each disjunct is added to Indices to distinguish the branches of the disjunction
  !,
  (
    (
      Disjuncts = (_ ; _)
      ->
      satisfy(violated_instance(Disjuncts,Indices), ModelIn, ModelOut) 
    ;
      % label active branch and ...
      assert(branch(Disjuncts)),
      %%%nl, write('Asserting: '), write(branch(Disjuncts)), 
      % ... investigate it
      satisfy(violated_instance(Disjuncts,[disjunct(Disjuncts)|Indices]), ModelIn, ModelOut)
    )
  ; 
    % switch to next branch and ...
    retract(branch(Disjuncts)),
    %%%nl, write('Retracting: '), write(branch(Disjuncts)), 
    assert(branch(Disjunct)),
    %%%nl, write('Asserting: '), write(branch(Disjunct)), 
    % ... investigate it
    satisfy(violated_instance(Disjunct,[disjunct(Disjunct)|Indices]), ModelIn, ModelOut)
  ).  
*/

satisfy(violated_instance(Head,Indices), ModelIn, ModelOut) :-
  % Head is an atom that can succeed or fail
  (
    % Head succeeds
    % can happen if Head occurs in a conjunction that fails because another conjunct fails
    user:call(Head)
    ->
    ModelOut =  ModelIn
  ; 
    % Head fails
    (
      % assimilate violated_instance(Head, Indices)
      (
        % if Head was derived with the help of the aggregating auxiliary axiom agg1 then it contains an uninstantiated discourse
        % referent that needs to be instantiated to prevent spurious solutions
        % example: "There are 2 red men. There are 3 blue men. No blue man is a red man. If there are 5 men then there is a cat.|- There is a cat."
        % where "cat" contains a discourse referent with a variable stemming from calculating "5 men"
        member(prolog_axiom(agg1), Indices),
        term_variables(Head, [Var])
        -> 
        Var = sk
      ;
        % no uninstantiated discourse referent
        true
      ),
/*
      % since Head must be satisfied the call to process_formulas_of_head/2 in prove_head/2 was not yet executed
      process_formulas_of_head(Head, Indices), 
*/
      (
        % tuple (Head, Indices) is not yet in the data base
        %%%nl, write('Trying to assert Head and Indices: '), write((Head, Indices)),
        \+ is_in_data_base(Head, Indices)
        ->
        % add Head to model
        %%%nl, write('Adding to model: '), write(Head),
        ModelOut =  [Head|ModelIn],
        %%%nl, write('ModelOut: '), write(ModelOut),
        % assert Head and Indices to the Prolog data base
        %%%nl, write('Asserting Head and Indices: '), write((Head, Indices)),
        user:assert(Head),
        term_hash(Head, HashOfHead),
        user:assert(indices(HashOfHead, Indices)),
        % 3 March 2021: Trace does not yet work correctly. Cannot be used in web-interface.
        %%%%%% generate_trace_paraphrase(ModelOut),  
        (
          % Head contains a call to a Prolog predicate encoded as a list
          % example: There is a result R of ["gcd", 15, 60, R]. |- A result is 15.
          % example: An answer A is generated by ["gcd", 15, 60, A]. |- An answer is 15.
          % example: There is a list L of ["append", [1,2,3], [4,5,6], L] and there is a maximum M1 of ["max_list", L, M1] and there is a minimum M2 of ["min_list", L, M2] and there is a result R of ["sum_list", [M1,M2], R].|- What is a result?
          % example: There is a list L of ["append", [1,2,3], [4,5,6], L] and there is a maximum M1 of ["max_list", L, M1] and there is a minimum M2 of ["min_list", L, M2] and there is a result R and R = M1 + M2.|- What is a result?
          subterm(list([string(Functor)|Arguments]), Head),
          transform_arguments(Arguments, TransformedArguments),
          % eliminate the case – caused by Satchmo's backtracking – that all arguments are variables 
          \+ forall(member(Arg, TransformedArguments), var(Arg)),
          % generate Prolog call
          Term =.. [Functor|TransformedArguments],
          % call Prolog predicate
          auxiliary_axioms:Term
        ;
          % Head does not contain a call to a Prolog predicate encoded as a list
          true
        )
      ;
        % tuple (Head, Indices) is already in the Prolog data base
        % leave model unchanged
        ModelOut =  ModelIn
      )
    ;
      % backtracking on assimilating violated_instance(Head,Indices) removes Head from model and ...
      %%%nl, write('Removing from model: '), write(Head),
      % ... Head and Indices from the Prolog data base
      %%%nl, write('Retracting Head and Indices: '), write((Head, Indices)),
      user:retract(Head),
      term_hash(Head, HashOfHead),
      user:retract(indices(HashOfHead, Indices)),
      !,
      fail	
    )
  ).
    

transform_arguments(Arguments, TransformedArguments) :-
  transform_arguments(Arguments, [], ReversedTransformedArguments),
  reverse(ReversedTransformedArguments, TransformedArguments).

transform_arguments([], TransformedArguments, TransformedArguments).

transform_arguments([Argument|Arguments], SoFar, TransformedArguments) :-
  (
    Argument = int(Integer)
    ->
    transform_arguments(Arguments, [Integer|SoFar], TransformedArguments)
  ;
    Argument = real(Real)
    ->
    transform_arguments(Arguments, [Real|SoFar], TransformedArguments)
  ;
    Argument = string(String)
    ->
    transform_arguments(Arguments, [String|SoFar], TransformedArguments)
  ;
    Argument = list(List)
    ->
    transform_arguments(List, TransformedList),
    transform_arguments(Arguments, [TransformedList|SoFar], TransformedArguments)
  ;
    % Argument is a skolem constant
    atom_chars(Argument, [s,k|_])
    ->
    (
      % skolem constant stands for proper name
      user: clauses(Clauses),
      member(satchmo_clause(true, object(_World, Argument, ProperNoun, named, na, eq, 1), [axiom(0)]), Clauses)
      ->
      transform_arguments(Arguments, [ProperNoun|SoFar], TransformedArguments)
    ;
      % skolem constant stands for variable or for its value
      b_getval(Argument, (Variable, _Index)),
      transform_arguments(Arguments, [Variable|SoFar], TransformedArguments)
    )
 ).
  
/*
generate_trace_paraphrase(Model) :-
  % replace all occurrences of a skolem term by the same variable
  findall(Skolem, (support:subterm(Skolem, Model), \+ Skolem = [], functor(Skolem, Functor, _), \+ Functor = [], sub_atom(Functor, 0, _, _, sk)), RawSkolems),
  % remove duplicates of skolem terms
  sort(RawSkolems, Skolems),
  replace_skolems(Skolems, Model, TransformedModel), 
  % create DRS Body
  create_drs_body(TransformedModel, DRSBody),
  % get indices involved
  findall(Index, member((_Element-Index/_), DRSBody), Indices),
  append(Indices, AllIndices),
  sort(AllIndices, IndicesInvolved),
  % try to generate an ACE paraphrase
  (
    % drs_to_ace/2 delivers a correct paraphrase
    drs_to_ace:drs_to_ace(drs([], DRSBody), Paraphrase),
    \+ member(['ERROR'], Paraphrase),
    \+ member([], Paraphrase),
    \+ Paraphrase = [[]]
    -> 
    nl, nl, write('Paraphrase: '), write(Paraphrase), nl, write('Axioms/Theorems involved: '), write(IndicesInvolved)
  ;
    % drs_to_ace/2 fails to deliver a correct paraphrase 
    true,
    nl, nl, write('Model: '), write(TransformedModel), nl, write('Axioms/Theorems involved: '), write(IndicesInvolved)
  ).
*/  
 
replace_skolems([], Model, Model).
  
replace_skolems([Skolem|Skolems], Model, TransformedModel) :-
  support:substitute(Skolem, _Variable, Model, IntermediateModel),
  replace_skolems(Skolems, IntermediateModel, TransformedModel).


create_drs_body(Model, DRSBody) :-
  create_drs_body(Model, [], DRSBody).
  
create_drs_body([], DRSBody, DRSBody).

create_drs_body([Element|Elements], SoFar, DRSBody) :-
  % get index of Element
  % duplicate Element to prevent instantiation of its variables
  duplicate_term(Element, Asserted_Element), 
  exists_asserted_atom(Asserted_Element, Index),
  % remove World argument
  Element =.. [Functor, _World|Rest],
  IntermediateElement =.. [Functor|Rest],
  % replace modified "be_..." by "be"
  replace_modified_be(IntermediateElement, TransformedElement), 
  % create DRS element
  create_drs_body(Elements, [TransformedElement-Index/_|SoFar], DRSBody).


replace_modified_be(ElementIn, ElementOut) :-
  (
    ElementIn =.. [predicate|Arguments],
    member(Modified_be, Arguments),
    (Modified_be == be_NP ; Modified_be == be_ID ; Modified_be == be_ADJ ; Modified_be == be_MOD)
    ->
    support:substitute(Modified_be, be, ElementIn, ElementOut)
  ;
    ElementOut = ElementIn
  ).


%---------------------------------------------------------------------------------------------------------
%
%  is_in_data_base(+Head, +Indices)
%
%  succeeds 
%    if there is a previously stored version of Head where the referent of the previously stored Head is a 
%    subset of the referent of the current Head
%    and 
%    both the previously stored and the current Head have the same Indices or Indices contains disjunct(Head)
%
%  prevents storing the same Head twice and preempts looping caused by clauses true => A, A => A, by clauses
%  true => A, A => B, B => A, or by clauses true => A, A & (¬A) => B, respectively true => A, A => (A v B)
%
%---------------------------------------------------------------------------------------------------------

is_in_data_base(Head, Indices) :- 
  (
    % construct a template of Head to check whether a previously stored version of Head exists in the data base
    % analyse Head
    Head =.. [Functor, World, Referent, Main|RemainingArguments],
    % get number of remaining arguments
    length(RemainingArguments, Length),
    % create a template list of the length of the remaining arguments
    length(OldRemainingArguments, Length),
    % construct the template OldHead of Head
    OldHead =.. [Functor, World, OldReferent, Main|OldRemainingArguments],
    % check whether OldHead is already in the data_base
    user:call(OldHead),
    % check whether the old referent is a subterm of the current referent 
    support:subterm(OldReferent, Referent),
    (
      % check whether the old and the current Head have the same indices
      term_hash(OldHead, OldHash),
      indices(OldHash, Indices)
      ->
      % catch cases true => A, A => A and true => A, A => B, B => A
      true  
    ;
      % check whether Indices contains disjunct(Head)
      memberchk(disjunct(Head), Indices)
      ->
      % catch case true => A, A & (¬A) => B, respectively true => A, A => (A v B)
      true  
    )
  )
  ->
  %%%nl, write('is_in_data_base: '), write((Head, Indices)),
  true.


%---------------------------------------------------------------------------------------------------------
%
%  operations on disjunctive branches
%
%---------------------------------------------------------------------------------------------------------

disjunctive_branches([]).


reset_disjunctive_branches :-
  retract(disjunctive_branches(_DisjunctiveBranches)),
  assert(disjunctive_branches([])).
  

convert_disjunction_into_list_of_disjuncts((Disjunct ; Disjuncts), [disjunct(Disjunct)|ListofDisjuncts]) :-
  (
    Disjuncts = (_ ; _)
    ->
    convert_disjunction_into_list_of_disjuncts(Disjuncts, ListofDisjuncts)
  ;
    ListofDisjuncts = [disjunct(Disjuncts)]
  ).


assimilate_closed_branch(ClosedBranch) :-
  % check whether the closed branch needs to be extended by indices of axioms "Name1 is Name2" occurring in
  % 'John is a man. Harry is a man. John is Harry.' |- 'There are how many men?'
  % prolog_axiom(w31) does not catch the index of the axiom 'John is Harry.'
  (
	% check whether prolog_axiom(w31) is involved
	member(prolog_axiom(w31), ClosedBranch),
    findall(Index,
				(
				user:identical_named_objects([Indices1], [Indices2], [Index]),
				member(Indices1, ClosedBranch),
				member(Indices2, ClosedBranch)
				),
            Indices)
    ->
    append(Indices, ClosedBranch, IntermediateClosedBranch),
    sort(IntermediateClosedBranch, NewClosedBranch)
  ;
    NewClosedBranch = ClosedBranch
  ),
  % assert closed branch if it was not previously asserted
  (
    \+ closed_branch(NewClosedBranch) 
    ->
    %%%nl, write('Asserting closed branch: '), write(closed_branch(NewClosedBranch)),
    assert(closed_branch(NewClosedBranch))
  ;
    true
  ).


collect_indices_of_all_inconsistent_clauses(Inconsistencies) :-
  (
    % there are disjunctive branches
    disjunctive_branches(DisjunctiveBranches),
    DisjunctiveBranches = [_|_]
    ->
    % prune open disjunctive branches
    prune_open_disjunctive_branches(DisjunctiveBranches, ClosedDisjunctiveBranches),
    (
      % there are closed disjunctive branches
      ClosedDisjunctiveBranches = [_|_]
      ->
      % collect and combine indices of closed disjunctive branches
      collect_and_combine_indices_of_closed_disjunctive_branches(ClosedDisjunctiveBranches, Inconsistencies1)
    ;
      % there are only partially closed disjunctive branches, i.e. the tableau is not closed
      % ClosedDisjunctiveBranches = []
      Inconsistencies1 = []
    )
  ;
    % there are no disjunctive branches
    Inconsistencies1 = []
  ),
  % collect indices of non-disjunctive closed branches
  findall(ClosedBranch, (closed_branch(ClosedBranch), \+ member(ClosedBranch, Inconsistencies1), \+ member(disjunct(_), ClosedBranch)), Inconsistencies2),
  append(Inconsistencies1, Inconsistencies2, Inconsistencies).


/* version without pruning
collect_indices_of_all_inconsistent_clauses(Inconsistencies) :-
  (
    % there are disjunctive branches
    disjunctive_branches(DisjunctiveBranches),
    DisjunctiveBranches = [_|_]
    ->
    % collect and combine indices of closed disjunctive branches
    collect_and_combine_indices_of_closed_disjunctive_branches(DisjunctiveBranches, Inconsistencies1)
  ;
    % there are no disjunctive branches
    Inconsistencies1 = []
  ),
  % collect indices of non-disjunctive closed branches
  findall(ClosedBranch, (closed_branch(ClosedBranch), \+ member(ClosedBranch, Inconsistencies1), \+ member(disjunct(_), ClosedBranch)), Inconsistencies2),
  append(Inconsistencies1, Inconsistencies2, Inconsistencies).
*/

prune_open_disjunctive_branches([], []).

prune_open_disjunctive_branches([DisjunctiveBranch|DisjunctiveBranches], Result) :-
  (
    % disjunctive branch is closed since all its branches are closed
    forall(member(Disjunct, DisjunctiveBranch), (closed_branch(ClosedBranch), member(Disjunct, ClosedBranch)))
    ->
    % keep disjunctive branch
    Result = [DisjunctiveBranch|ClosedDisjunctiveBranches]
  ;
    % disjunctive branch is open since at least one of its branches is not closed
    % discard open disjunctive branch
    Result = ClosedDisjunctiveBranches
  ),
  prune_open_disjunctive_branches(DisjunctiveBranches, ClosedDisjunctiveBranches).


collect_and_combine_indices_of_closed_disjunctive_branches([], Inconsistencies) :-
  % collect all closed branches that do not contain conditions of the form disjunct(_)  
  findall(ClosedBranch, (closed_branch(ClosedBranch), \+ member(disjunct(_), ClosedBranch)), Inconsistencies).

collect_and_combine_indices_of_closed_disjunctive_branches([ClosedDisjunctiveBranch|ClosedDisjunctiveBranches], Inconsistencies) :-
  % collect closures of each disjunct of the closed disjunctive branch
  collect_closures_of_each_disjunct(ClosedDisjunctiveBranch),
  % continue loop
  collect_and_combine_indices_of_closed_disjunctive_branches(ClosedDisjunctiveBranches, Inconsistencies).


collect_closures_of_each_disjunct(DisjunctiveBranch) :-
  findall(OneClosure, one_closure(DisjunctiveBranch, OneClosure), AllClosures),
  forall(member(OneClosure, AllClosures), 
                                         (
                                           % generate partial closure ...
                                           append(OneClosure, RawPartialClosure),
                                           % ... eliminate duplicate elements and ...
                                           sort(RawPartialClosure, PartialClosure),
                                           %%%nl, write('PartialClosure: '), write(PartialClosure),
                                           % ... add it to closed branches if not yet present
                                           (
                                             \+ closed_branch(PartialClosure) 
                                             -> 
                                             assert(closed_branch(PartialClosure)) 
                                           ; 
                                             true
                                           )
                                         )
        ).
 
 
one_closure([], []).

one_closure([Disjunct|Disjuncts], [ReducedClosedBranch|ReducedClosedBranches]) :-
  % find closed branch containing Disjunct and ...
  closed_branch(ClosedBranch),
  % ... eliminate Disjunct and ...
  select(Disjunct, ClosedBranch, ReducedClosedBranch),
  one_closure(Disjuncts, ReducedClosedBranches).


%---------------------------------------------------------------------------------------------------------
%
%  is_candidate(+Body, +RecentlyAdded)
%  
%  select a clause Body -> Head if 
%    (1) Body and RecentlyAdded have at least one common element, or 
%    (2) at least one element of Body can be proved via an auxiliary axiom, or 
%    (3) all elements of Body are formulas
%    (4) Body is negation as failure
%
%  condition (1) has higher priority than condition (2) because condition (2) currently is too general;
%  however, condition (2) is necessary since Body can consist of a single element that needs to be proved   
%  via an auxiliary axiom – e.g. to prove "there are 2 apples" from "there are 3 apples"
%
%---------------------------------------------------------------------------------------------------------

is_candidate(Body, RecentlyAdded) :-
  \+ RecentlyAdded = [],
  conjunction_to_list(Body, BodyAsList),
  (
    % Body and RecentlyAdded have at least one common element
    \+ intersection(BodyAsList, RecentlyAdded, [])
    ->
    true
  ;
    % at least one element of Body can be proved via an auxiliary axiom
    % inactivate this test for the initial round when only clauses with body "true" are to be selected
    \+ RecentlyAdded = [true],
    member(Element, BodyAsList),
    prolog_axiom(Element, _IndicesSoFar, _Indices)
    ->
    true
  ;
    % all elements of Body are formulas
    % inactivate this test for the initial round when only clauses with body "true" are to be selected
    \+ RecentlyAdded = [true],
    forall(member(Element, BodyAsList), Element=formula(_,_,_,_))
    ->
    true
  ;
    % Body is negation as failure
    % allow this test if there are but two clauses one of which has the Body naf(_) as in the case
    % If it is not provable that there is a dog then there is a cat. |- There is a cat.
    % otherwise inactivate this test for the initial round when only clauses with body "true" are to be selected
    (user:clauses([_,_]) ; \+ RecentlyAdded = [true]),
    Body = naf(_)
    ->
    true
  ).


%---------------------------------------------------------------------------------------------------------
%
%  arithmetic
%
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
% process_formulas_of_body(+Body, +IndexOfBody, -IndicesOfFormulas)
%
%---------------------------------------------------------------------------------------------------------

process_formulas_of_body(Body, IndexOfBody, IndicesOfFormulas) :-
  % find formulas of body
  findall((formula(LHS, Operator, RHS), IndexOfBody), support:subterm(formula(_World, LHS, Operator, RHS), Body), FormulasIndices), 
  % evaluate formulas
  evaluate_formulas_of_body(FormulasIndices, IndicesOfFormulas).


%---------------------------------------------------------------------------------------------------------
%
% evaluate_formulas_of_body(+FormulasIndices, -IndicesOfFormulas)
%
%---------------------------------------------------------------------------------------------------------

evaluate_formulas_of_body(FormulasIndices, IndicesOfFormulas) :-
  % formulas serve as tests that can succeed or fail depending on their arguments
  %
  % formulas with only instantiated variables will succeed or fail depending on the numerical values 
  %
  % formulas containing uninstantiated variables can succeed or fail in 2 cases
  %
  %   (1) by being interpreted not as tests but as assignments, as for example 'A=B. |- X=1.' where the
  %       formula 'X=1' would succeed by assignment though there is no previous value for X; to eliminate
  %       these unwanted assignments all occurring variables should be instantiated to a number before 
  %       the formulas are executed 
  %
  %   (2) in cases like 'X>1. |- X>0.' (success) or 'X>1. |- X>2.' (failure)
  %
  % first all formulas are evaluated together to take care of delayed instantiations, contradictions and 
  % unwanted assigments (1), then we individually evaluate formulas whose variables are not instantiated (2)
  (
    % all variables – looked up via the related skolem terms – are instantiated to a number
    forall( (
              support:subterm(Skolem, FormulasIndices), 
              functor(Skolem, Functor, _), 
              \+ Functor = [],
              sub_atom(Functor, 0, _, _, sk), 
              b_getval(Functor, (Variable, _IndexOfSkolem))
            ),
            number(Variable)
          )
    ->
    convert_formulas(FormulasIndices, ConvertedFormulasIndices),
    %%%nl, write((FormulasIndices, ConvertedFormulasIndices)),
    (
      % execution succeeds
      execute_formulas(ConvertedFormulasIndices)
      ->
      % get indices of formulas
      findall(Indices, member((_Formula, Indices), ConvertedFormulasIndices), AllIndices),
      flatten(AllIndices, FlattenedAllIndices),
      sort(FlattenedAllIndices, IndicesOfFormulas) 
      %%%, nl, write('success1 '), write(ConvertedFormulasIndices), write(' '), write(IndicesOfFormulas)
    ;
      % execution fails 
      % arithmetic contradiction brought about by the current variable instantiations
      % backtrack to find alternative variable instantiations
      %%%nl, write('failure1 '), write(ConvertedFormulasIndices),
      fail
    )
  ;
    % not all variables are instantiated to a number
    % note: instead of processing just the formulas that contain uninstantiated variables it seems simpler to process all formulas
    (
      % try proving the formulas from the Prolog data base
      convert_formulas(FormulasIndices, ConvertedFormulasIndices),
      findall((formula(LHSA, OperatorA, RHSA), IndexA), exists_asserted_atom(formula(_World, LHSA, OperatorA, RHSA), IndexA), AssertedFormulasIndices),
      findall(Subset, subsets_in_size_order(AssertedFormulasIndices, Subset), SortedSubsets),
      member(OneSubset, SortedSubsets),
      once(convert_formulas(OneSubset, ConvertedOneSubset)),
      % execution succeeds
      execute_formulas(ConvertedOneSubset),
      entailed_formulas(ConvertedFormulasIndices)
      ->
      % get indices of formulas
      append(ConvertedFormulasIndices, ConvertedOneSubset, ConvertedAllFormulasIndices),
      findall(Indices, member((_Formula, Indices), ConvertedAllFormulasIndices), AllIndices), 
      flatten(AllIndices, FlattenedAllIndices),
      sort(FlattenedAllIndices, IndicesOfFormulas) 
      %%%, nl, write('success2 '), write(ConvertedAllFormulasIndices), write(' '), write(IndicesOfFormulas)
    ;
      % execution fails 
      % arithmetic contradiction brought about by the current variable instantiations
      % backtrack to find alternative variable instantiations
      %%%nl, write('failure2 '), write(ConvertedAllFormulasIndices),
      fail
    )
  ).


%---------------------------------------------------------------------------------------------------------
%
% process_formulas_of_fact_clauses(+Clauses)
%
%---------------------------------------------------------------------------------------------------------

process_formulas_of_fact_clauses(Clauses) :-
  % find formulas of fact clauses
  findall((formula(LHS, Operator, RHS), Index),
           (member(satchmo_clause(true, Head, Index), Clauses), support:subterm(formula(_World, LHS, Operator, RHS), Head)), 
          FormulasIndices), 
  % evaluate formulas
  evaluate_formulas_of_head(FormulasIndices).

%---------------------------------------------------------------------------------------------------------
%
% process_formulas_of_head(+Head, +IndexOfHead)
%
%---------------------------------------------------------------------------------------------------------

process_formulas_of_head(Head, IndexOfHead) :-
  % find formulas of head
  findall((formula(LHS, Operator, RHS), IndexOfHead), support:subterm(formula(_World, LHS, Operator, RHS), Head), FormulasIndices),
  % evaluate formulas
  evaluate_formulas_of_head(FormulasIndices).


%---------------------------------------------------------------------------------------------------------
%
% evaluate_formulas_of_head(+FormulasIndices)
%
%---------------------------------------------------------------------------------------------------------

evaluate_formulas_of_head(FormulasIndices) :-
  (
    % Prolog call encoded as list in a formula
    % example: There is a result R of a function F and F = ["gcd", 12, 33, R]. |- A result is 3.
    % example: There is a result R of a function F and F = ["gcd", 12, 33, R]. |- What is a result?
    subterm(list([string(Functor)|Arguments]), FormulasIndices),
    transform_arguments(Arguments, TransformedArguments),
    % generate Prolog call
    Term =.. [Functor|TransformedArguments],
    % call Prolog predicate
    auxiliary_axioms:Term
  ;
    % arithmetic formula
    evaluate_formulas_of_head1(FormulasIndices)
  ).

evaluate_formulas_of_head1(FormulasIndices) :-
  convert_formulas(FormulasIndices, ConvertedFormulas),
  %%%nl, write((FormulasIndices, ConvertedFormulas)),
  (
    % execution succeeds
    execute_formulas(ConvertedFormulas)
    ->
    true
  ;
    % execution fails which means that there are arithmetic contradictions or CLPQR errors (e.g. square root of a negative number)
    % generate a warning message and ...
    add_error_message_once(race, '', 'Arithmetic axioms are inconsistent or could not be evaluated.', 'Check axioms.'),
    % ... get indices of all arithmetically contradictory subsets of the axioms
    % Note: all subsets are generated, succeeding ones are eliminated here, non-minimally failing ones are eliminated later thus only
    % minimally failing ones are eventually reported; but see below for spurious solutions.
    forall(
            (
              generate_subset(FormulasIndices, SubsetOfFormulasIndices), 
              convert_formulas(SubsetOfFormulasIndices, ConvertedSubsetOfFormulas)
            ),
            (
              % execution of the chosen subset suceeds
              execute_formulas(ConvertedSubsetOfFormulas)
              ->
              true
            ;
              % execution  of the chosen subset fails which means that it is arithmetically contradictory
              % assimilate indices of arithmetically contradictory subset
              findall(Index, member((_Formula, Index), SubsetOfFormulasIndices), RawIndices),
              flatten(RawIndices, FlattenedRawIndices),
              sort(FlattenedRawIndices, Indices),
              assimilate_closed_branch(Indices), 
              % retract any closed branch that refers only to one axiom/theorem also contained in Indices
              % example: check_consistency('There is a man. If there is a man then A is 1 and A is 2.', [], M, T, P).
              % generates two closed branches [axiom(2)], and [axiom(1), axiom(2)] where [axiom(2)] is spurious
              % RACE would report only the spurious solution since it is minimal
              % to prevent this the spurious solution [axiom(2)] is eliminated here
              (
                closed_branch([ClosedBranch]),
                member(ClosedBranch, Indices),
                [ClosedBranch] \= Indices
                ->
                retract(closed_branch([ClosedBranch]))
              ;
                true
              )
            )  
          )
   ).


%---------------------------------------------------------------------------------------------------------
%
% convert_formulas(+Formulas, -ConvertedFormulas)
%
%---------------------------------------------------------------------------------------------------------

convert_formulas([], []).

convert_formulas(Formulas, ConvertedFormulas) :-
  % collect LHS or RHS that are skolem terms
  collect_LHS_RHS_Skolems(Formulas, LHSandRHSSkolems),
  % convert formulas
  convert_formulas1(Formulas, LHSandRHSSkolems, ConvertedFormulas).
  
collect_LHS_RHS_Skolems(Formulas, LHSandRHSSkolems) :-
  collect_LHS_RHS_Skolems(Formulas, [], LHSandRHSSkolems).
  
collect_LHS_RHS_Skolems([], Skolems, Skolems).

collect_LHS_RHS_Skolems([(formula(LHS, _Operator, RHS), _Index) | RestFormulas], SkolemsSoFar, Skolems) :-
  (
    % LHS or RHS is a skolem term
    ((functor(LHS, Functor, _), \+ Functor = [], sub_atom(Functor, 0, _, _, sk)) ; (functor(RHS, Functor, _), \+ Functor = [], sub_atom(Functor, 0, _, _, sk)))
    ->
    collect_LHS_RHS_Skolems(RestFormulas, [Functor|SkolemsSoFar], Skolems)
  ;
    % neither LHS nor RHS is a skolem term
    collect_LHS_RHS_Skolems(RestFormulas, SkolemsSoFar, Skolems)
  ).

convert_formulas1([], _LHSandRHSSkolems, []).

convert_formulas1([(formula(LHS, Operator, RHS), Index) | RestFormulas], LHSandRHSSkolems, [(ConvertedFormula, IndexOut) | ConvertedRestFormulas])  :-
  % index skolem terms of the formula
  (
    % LHS is a single skolem term
    % index the skolem term by the indices of the other skolem terms of the formula
    functor(LHS, LHSFunctor, _), 
    \+ LHSFunctor = [],
    sub_atom(LHSFunctor, 0, _, _, sk)
    ->
    findall(IndexOfSkolem, 
            (support:subterm(Skolem, RHS), 
             functor(Skolem, Functor, _), 
             \+ Functor = [],
             sub_atom(Functor, 0, _, _, sk), 
             b_getval(Functor, (_Variable, IndexOfSkolem))), 
             IndicesOfSkolems),
    b_getval(LHSFunctor, (Variable, LHSIndexOfSkolem)), 
    flatten([Index, LHSIndexOfSkolem|IndicesOfSkolems], FlattenedIndicesOfAllSkolems),
    sort(FlattenedIndicesOfAllSkolems, SortedFlattenedIndicesOfAllSkolems),
    b_setval(LHSFunctor, (Variable, SortedFlattenedIndicesOfAllSkolems))
  ;
    % RHS is a single skolem term
    % index the skolem term by the indices of the other skolem terms of the formula
    functor(RHS, RHSFunctor, _), 
    \+ RHSFunctor = [],
    sub_atom(RHSFunctor, 0, _, _, sk)
    ->
    findall(IndexOfSkolem, 
            (support:subterm(Skolem, LHS), 
             functor(Skolem, Functor, _), 
             \+ Functor = [],
             sub_atom(Functor, 0, _, _, sk), 
             b_getval(Functor, (_Variable, IndexOfSkolem))), 
            IndicesOfSkolems),
    b_getval(RHSFunctor, (Variable, RHSIndexOfSkolem)),
    flatten([Index, RHSIndexOfSkolem|IndicesOfSkolems], FlattenedIndicesOfAllSkolems),
    sort(FlattenedIndicesOfAllSkolems, SortedFlattenedIndicesOfAllSkolems),
    b_setval(RHSFunctor, (Variable, SortedFlattenedIndicesOfAllSkolems))
  ;
    % neither LHS nor RHS is a single skolem term
    % index all skolem terms by the indices of all skolem terms of the formula
    findall(Skolem, 
            (support:subterm(Skolem, (LHS, RHS)), 
             functor(Skolem, Functor, _), 
             \+ Functor = [],
             sub_atom(Functor, 0, _, _, sk)), 
            Skolems),
    findall(IndexOfSkolem, 
            (support:subterm(Skolem, (LHS, RHS)), 
             functor(Skolem, Functor, _), 
             \+ Functor = [],
             sub_atom(Functor, 0, _, _, sk), 
             b_getval(Functor, (_Variable, IndexOfSkolem))), 
            IndicesOfSkolems),
    % get skolem terms that depend on the LHS and RHS skolem terms
    subtract(Skolems, LHSandRHSSkolems, SkolemsDependentOnLHSandRHSSkolems),
    update_indices_of_skolem_terms(SkolemsDependentOnLHSandRHSSkolems, Index, IndicesOfSkolems)
  ),
  % convert the formula
  % get start value IndicesIn of indices
  append(Index, IndicesOfSkolems, RawIndices),
  flatten(RawIndices, FlattenedRawIndices),
  sort(FlattenedRawIndices, IndicesIn),
  % convert LHS and RHS
  convert(LHS, ConvertedLHS, IndicesIn, IndexIntermediate),
  convert(RHS, ConvertedRHS, IndexIntermediate, IndexOut),
  (
    % convert ACE's numerical non-equality operator to Prolog's numerical non-equality operator
    Operator = (\=)
    ->
    ConvertedOperator = (=\=)
  ;
    ConvertedOperator = Operator
  ),
  ConvertedFormula =.. [ConvertedOperator, ConvertedLHS, ConvertedRHS], 
  !,
  convert_formulas1(RestFormulas, LHSandRHSSkolems, ConvertedRestFormulas).


% update the indices of skolem terms arithmetically depending on other skolem terms
% example: in A=1, B=2, A+B=C+2, the skolem term C depends on the skolem terms A and B
% note: forall/2 cannot be used since the second argument of b_setval/2 would not get instantiated 
% skip non-atomic skolem terms
update_indices_of_skolem_terms([], _Index, _IndicesOfSkolems).

update_indices_of_skolem_terms([Skolem|Skolems], Index, IndicesOfSkolems) :-
  (
    atomic(Skolem)
    ->
    b_getval(Skolem, (Variable, IndexOfSkolem)),
    append([Index, IndexOfSkolem, IndicesOfSkolems], RawIndicesOfAllSkolems),
    flatten(RawIndicesOfAllSkolems, FlattenedIndicesOfAllSkolems),
    sort(FlattenedIndicesOfAllSkolems, SortedFlattenedIndicesOfAllSkolems),
    b_setval(Skolem, (Variable, SortedFlattenedIndicesOfAllSkolems)),
    %%%nl, write(b_setval(Skolem, (Variable, SortedFlattenedIndicesOfAllSkolems))),
    update_indices_of_skolem_terms(Skolems, Index, IndicesOfSkolems)
  ;
    update_indices_of_skolem_terms(Skolems, Index, IndicesOfSkolems)
  ).


convert(expr(Operator, LHS, RHS), ConvertedExpression, IndexIn, IndexOut) :-
  (Operator = + ; Operator = - ; Operator = * ; Operator = / ; Operator = ^)
  ->
  convert(LHS, ConvertedLHS, IndexIn, IndexIntermediate),
  convert(RHS, ConvertedRHS, IndexIntermediate, IndexOut),
  ConvertedExpression =.. [Operator, ConvertedLHS, ConvertedRHS].

convert(Skolem, Variable, IndexIn, IndexOut) :-
  functor(Skolem, Functor, _), 
  \+ Functor = [],
  sub_atom(Functor, 0, _, _, sk),
  b_getval(Functor, (Variable, Index)),
  (
    % Variable is instantiated to a number
    number(Variable) 
    ->
    flatten([Index|IndexIn], FlattenedIndices),
    sort(FlattenedIndices, IndexOut)
  ;
    % Variable is not yet instantiated to a number
    IndexOut = IndexIn
  ).

convert(X, X, Index, Index) :-
  var(X),
  !.
  
convert(+, +, Index, Index) :- 
  !.

convert(-, -, Index, Index) :- 
  !.

convert(*, *, Index, Index) :- 
  !.

convert(/, /, Index, Index) :- 
  !.

convert(^, ^, Index, Index) :- 
  !.

convert(int(X), X, Index, Index) :- 
  !.

convert(real(X), X, Index, Index) :- 
  !.


%---------------------------------------------------------------------------------------------------------
%
% calls to clpr
%
%   execute_formulas(+Formulas)
%   add Formulas to constraint store and evaluate them
%
%   entailed_formulas(+Formulas)
%   Formulas are entailed by current constraint store
%
%---------------------------------------------------------------------------------------------------------

execute_formulas([]).

execute_formulas([(Formula, _Index)|Formulas]) :-
  nf_r:{Formula},
  !, 
  execute_formulas(Formulas).

  
entailed_formulas([]).

entailed_formulas([(Formula, _Index)|Formulas]) :-
  nf_r:entailed(Formula),
  entailed_formulas(Formulas).
 
 
%--------------------------------------------------------------------------------------------------------
%
%  arithmetic workplace
%
%---------------------------------------------------------------------------------------------------------

/*
process_arithmetic(Clauses) :-

  user:clauses(Clauses),
  findall({formula(A, B, C)}, (support:subterm(formula(sk1, A, B, C), Clauses), ground(A), ground(B), ground(C)), Formulas),
  findall(Index, (member({formula(A, B, C)}, Formulas), member(satchmo_clause(true, formula(sk1, A, B, C), Index), Clauses)), IndicesOfFormulas),
  % example Formulas = [formula(expr(+, expr(*, int(4), sk3), expr(*, int(2), sk6)), =, int(260)), formula(expr(+, sk3, sk6), =, int(100))],
  substitute_skolem_terms_by_variables(Formulas, FormulasWithVariables, Substitutions),
  convert_formulas(FormulasWithVariables, ConvertedFormulasWithVariables),
  % example ConvertedFormulasWithVariables = [{4*_G280+2*_G228=260}, {_G280+_G228=100}]
  execute_formulas(ConvertedFormulasWithVariables),
  % example after execution: ConvertedFormulasWithVariables = [{4*30+2*70=260}, {30+70=100}]
  % i.e. all variables are now instantiated by values, also in Substitutions
  findall((Noun, Value, Index),
           (
             member(Skolem-Value, Substitutions), 
             exists_asserted_atom(object(World, Skolem, LinkNoun, _, _, _, _), Index),
             exists_asserted_atom(relation(World,Skolem, LinkNoun, of, NounReferent), Index),
             exists_asserted_atom(object(World, NounReferent, Noun, _, _, _, _), Index)
           ),
         NounsValuesIndices
         ),
  collect_results_and_indices(NounsValuesIndices, NounsValues, IndividualIndices),
  member(satchmo_clause(Body, fail, _Index), Clauses),
  support:subterm(query(World, A, what), Body),
  support:subterm(relation(World, _Skolem, LinkNoun, of, Noun), Body),
  support:subterm(object(World, _Skolem, Noun, _, _, _, _), Body),
  member((Noun-Value), NounsValues),
  NounValue=[Noun-Value],
  append(IndividualIndices, IndicesOfFormulas, RawIndices),
  flatten(RawIndices, FlattenedIndices),
  sort(FlattenedIndices, Indices).
*/
/*
process_arithmetic(PreliminaryModel, Model) :-
  % evaluate expressions that could not be evaluated before because some elements were missing
  evaluate_all_still_unevaluated_expressions(PreliminaryModel, Model),
  % check for numerical inconsistencies
  (
    % two different arithmetic terms are claimed to be identical, e.g. "1 is 2."
    exists_asserted_atom(predicate(_World, _PredicateReferent, be_NP, LeftSide, RightSide), Indices),
    (LeftSide = int(NumberLeft) ; LeftSide = real(NumberLeft)),
    (RightSide = int(NumberRight) ; RightSide = real(NumberRight)),
    \+ NumberLeft = NumberRight
    ->
    % create warning message
    Indices = [axiom(Index)],
    atomic_list_concat(['Axioms are inconsistent, anything can be derived. In axiom ', Index, ' the numbers ', NumberLeft, ' and ', NumberRight, ' are erroneously claimed to be identical.'], MessageText),
    add_warning_message_once(race, '', MessageText, 'Check axioms.'),
    % assimilate indices of closed branch
    assimilate_closed_branch(Indices)
  ;
    % two distinct arithmetical assigments are contradictory, e.g. "X is 1. X is 2."
    exists_asserted_atom(predicate(_World, PredicateReferent1, be_NP, LeftSide, RightSide1), Indices1),
    functor(LeftSide, Name, _Arity), \+ Name = [], sub_atom(Name, 0, _, _, sk),
    (RightSide1 = int(NumberRight1) ; RightSide1 = real(NumberRight1)),
    exists_asserted_atom(predicate(_World, PredicateReferent2, be_NP, LeftSide, RightSide2), Indices2),
    (RightSide2 = int(NumberRight2) ; RightSide2 = real(NumberRight2)),
    % assigments are distinct
    \+ PredicateReferent1 = PredicateReferent2,
%%%    !,
    \+ RightSide1 = RightSide2
    ->
    % create warning message
    Indices1 = [axiom(Index1)],
    Indices2 = [axiom(Index2)],
    atomic_list_concat(['Axioms are inconsistent, anything can be derived. Axiom ', Index1, ' and axiom ', Index2, ' erroneously assign different numbers to the same term.'], MessageText),
    add_warning_message(race, '', MessageText, 'Check axioms.'),
    % assimilate indices of closed branch
    assimilate_closed_branch([axiom(Index1), axiom(Index2)])
  ;
    true
  ). 
*/
/*
evaluate_all_still_unevaluated_expressions(PreliminaryModel, Model):-
  findall((predicate(World, PredicateReferent, be_NP, LeftSide, RightSide), Index) , 
             (exists_asserted_atom(predicate(World, PredicateReferent, be_NP, LeftSide, RightSide), Index), 
             (LeftSide = expr(_,_,_) ; RightSide = expr(_,_,_))),
             RawAllPredicatesWithExpressionsPlusIndex),
  % remove any duplicates
  sort(RawAllPredicatesWithExpressionsPlusIndex, AllPredicatesWithExpressionsPlusIndex),           
  evaluate_all_predicates_with_expressions(AllPredicatesWithExpressionsPlusIndex, PreliminaryModel, Model).
*/
/*
evaluate_all_predicates_with_expressions([], Model, Model).

evaluate_all_predicates_with_expressions([(Predicate, IndexOfPredicate)|RestPredicatesPlusIndex], PreliminaryModel, Model) :-
  (
    % right side is an expression
    Predicate = predicate(World, PredicateReferent, be_NP, LeftSide, expr(Operator, Argument1, Argument2)),
    \+ LeftSide = expr(_, _, _)
    ->
    evaluate_one_expression(expr(Operator, Argument1, Argument2), IndexOfPredicate, final_attempt, Value, Indices),
    % update the PreliminaryModel
    select(Predicate, PreliminaryModel, ReducedModel),
    IntermediateModel = [predicate(World, PredicateReferent, be_NP, LeftSide, Value)|ReducedModel],
    % update the Prolog data base
    %%%nl, write('Retracting Predicate and IndexOfPredicate: '), write((Predicate, IndexOfPredicate)),
    user:retract(Predicate),
    term_hash(Predicate, HashOfPredicate),
    user:retract(indices(HashOfPredicate, _)),
    %%%nl, write('Asserting ModifiedPredicate and IndicesOfModifiedPredicate: '), write((predicate(World, PredicateReferent, be_NP, LeftSide, Value), Indices)),
    user:assert(predicate(World, PredicateReferent, be_NP, LeftSide, Value)),
    term_hash(predicate(World, PredicateReferent, be_NP, LeftSide, Value), HashOfModifiedPredicate),
    user:assert(indices(HashOfModifiedPredicate, Indices))
  ;
    % left side is an expression
    Predicate = predicate(World, PredicateReferent, be_NP, expr(Operator, Argument1, Argument2), RightSide),
    \+ RightSide = expr(_, _, _)
    ->
    evaluate_one_expression(expr(Operator, Argument1, Argument2), IndexOfPredicate, final_attempt, Value, Indices),
    % update the PreliminaryModel
    select(Predicate, PreliminaryModel, ReducedModel),
    IntermediateModel = [predicate(World, PredicateReferent, be_NP, Value, RightSide)|ReducedModel],
    % update the Prolog data base
    %%%nl, write('Retracting Predicate and IndexOfPredicate: '), write((Predicate, IndexOfPredicate)),
    user:retract(Predicate),
    term_hash(Predicate, HashOfPredicate),
    user:retract(indices(HashOfPredicate, _)),
    %%%nl, write('Asserting ModifiedPredicate and IndicesOfModifiedPredicate: '), write((predicate(World, PredicateReferent, be_NP, Value, RightSide), Indices)),
    user:assert(predicate(World, PredicateReferent, be_NP, Value, RightSide)),
    term_hash(predicate(World, PredicateReferent, be_NP, Value, RightSide), HashOfModifiedPredicate),
    user:assert(indices(HashOfModifiedPredicate, Indices))
  ;
    % both sides are expressions
    Predicate = predicate(World, PredicateReferent, be_NP, expr(Operator, Argument1L, Argument2L), expr(Operator, Argument1R, Argument2R))
    ->
    evaluate_one_expression(expr(Operator, Argument1L, Argument2L), IndexOfPredicate, final_attempt, ValueL, IndicesL),
    evaluate_one_expression(expr(Operator, Argument1R, Argument2R), IndexOfPredicate, final_attempt, ValueR, IndicesR),
    % update the PreliminaryModel
    select(Predicate, PreliminaryModel, ReducedModel),
    IntermediateModel = [predicate(World, PredicateReferent, be_NP, ValueL, ValueR)|ReducedModel],
    % update the Prolog data base
    %%%nl, write('Retracting Predicate and IndexOfPredicate: '), write((Predicate, IndexOfPredicate)),
    user:retract(Predicate),
    term_hash(Predicate, HashOfPredicate),
    user:retract(indices(HashOfPredicate, IndexOfPredicate)),
    %%%nl, write('Asserting ModifiedPredicate and IndicesOfModifiedPredicate: '), write((predicate(World, PredicateReferent, be_NP, ValueL, ValueR), Indices)),
    user:assert(predicate(World, PredicateReferent, be_NP, ValueL, ValueR)),
    term_hash(predicate(World, PredicateReferent, be_NP, ValueL, ValueR), HashOfModifiedPredicate),
    append(IndicesL, IndicesR, IndicesIntermediate),
    sort(IndicesIntermediate, Indices),
    user:assert(indices(HashOfModifiedPredicate, Indices))
  ),
  evaluate_all_predicates_with_expressions(RestPredicatesPlusIndex, IntermediateModel, Model).
*/
/*
evaluate_one_expression(expr(Operator, Argument1, Argument2), IndexOfOriginalExpression, WhichAttempt, Value, Indices) :-
  convert_argument_to_value(Argument1, IndexOfOriginalExpression, WhichAttempt, Value1, Indices1), 
  convert_argument_to_value(Argument2, IndexOfOriginalExpression, WhichAttempt, Value2, Indices2), 
  (
    % expression is fully instantiated
    number(Value1),
    number(Value2)
    ->
    % use Prolog's "is"-operator to evaluate the expression
    Expression =.. [Operator, Value1, Value2],
    RawValue is Expression,
    % convert to ACE representation
    (
      float(RawValue)
      ->
      Value=real(RawValue)
    ;
      Value=int(RawValue)
    ),
    append(Indices1, Indices2, IntermediateIndices),
    sort(IntermediateIndices, Indices)
  ;
    % expression is not fully instantiated
    Value = expr(Operator, Argument1, Argument2),
    Indices = IndexOfOriginalExpression
  ).
*/
/*
convert_argument_to_value(Argument, IndexOfOriginalExpression, WhichAttempt, Value, Indices) :-
  (
    % argument is an integer
    Argument = int(Value)
    -> 
    Indices = IndexOfOriginalExpression
  ;
    % argument is a real
    Argument = real(Value)
    -> 
    Indices = IndexOfOriginalExpression
  ;
    % argument is an expression
    Argument = expr(Operator, Argument1, Argument2)
    -> 
    evaluate_one_expression(expr(Operator, Argument1, Argument2), IndexOfOriginalExpression, WhichAttempt, RawValue, Indices),
    (
      % RawValue is an integer
      RawValue = int(Value)
      -> 
      true
    ;
      % RawValue is a real
      RawValue = real(Value)
      -> 
      true
    ;
      % expression could not be evaluated
      RawValue = expr(Operator, Argument1, Argument2)
      -> 
      Value = expr(Operator, Argument1, Argument2),
      Indices = IndexOfOriginalExpression
    )
  ;
    % argument is skolem term pointing to a value defined elsewhere
    functor(Argument, Name, _Arity), \+ Name = [], sub_atom(Name, 0, _, _, sk)
    -> 
    (
      % value of skolem term is found
      (
        exists_asserted_atom(predicate(_World, _PredicateReferent, be_NP, Argument, RawValue), Indices)
      ;
        exists_asserted_atom(predicate(_World, _PredicateReferent, be_NP, RawValue, Argument), Indices)
      ),
      % if RawValue is an expression it should not contain Argument which would indicate a recursive definition
      \+ support:subterm(Argument, RawValue)
      ->
      convert_argument_to_value(RawValue, IndexOfOriginalExpression, WhichAttempt, Value, _Indices)
    ;
      % value of skolem term cannot be found, i.e. expression contains uninstantiated variables
      % differentiate between initial and final attempt to evaluate the expression
      (
        % initial attempt
        WhichAttempt = initial_attempt
        ->
        % set value to expression and wait for final attempt to evaluate the expression
        Value = Argument,
        Indices = IndexOfOriginalExpression
      ;
        % final attempt
        WhichAttempt = final_attempt
        ->
        % set Value to 0 to be able to continue without arithmetic errors generated by SWI Prolog
        Value = 0,
        Indices = IndexOfOriginalExpression, 
        % create error message
        % note: since the ACE form of the expression is not available the expression is not shown in the error message
        IndexOfOriginalExpression = [SourceIndex],
        SourceIndex =.. [Source, Index],
        atomic_list_concat(['An expression in ', Source, ' ', Index, ' cannot be evaluated since some of its terms do not evaluate to numbers, or it refers directly or indirectly to itself.'], MessageText),
        add_error_message(race, Index-'', MessageText, 'Check input.')
      )
    )
  ).
*/
/*
evaluate(Expression, OriginalExpression, Value) :-
  (
    % recursively evaluate Expression
    Expression = expr(Operator, Expression1, Expression2)
    ->
    evaluate(Expression1, OriginalExpression, Value1),
    evaluate(Expression2, OriginalExpression, Value2),
    ValueOfExpression =.. [Operator, Value1, Value2], 
    Value is ValueOfExpression
  ;
    % Expression is a number
    (Expression = int(Number) ; Expression = real(Number)),
    number(Number)
    ->
    Value = Number
  ;
    % Expression contains variables
    % set Value to 0 to be able to continue without arithmetic warnings generated by SWI Prolog
    Value = 0,
    term_to_atom(OriginalExpression, OriginalExpressionAtom),
    atomic_list_concat(['Not all variables of the expression ', OriginalExpressionAtom, ' are instantiated before evaluation.'], MessageText),
    add_warning_message_once(race, '', MessageText, 'Check input.')
  ).
*/
  
 
%--------------------------------------------------------------------------------------------------------
%
%  clean_up_from_previous_run
%
%---------------------------------------------------------------------------------------------------------

clean_up_from_previous_run :-
  reset_disjunctive_branches,
  retractall(closed_branch(_)),
  retractall(branch(_)).


%---------------------------------------------------------------------------------------------------------
