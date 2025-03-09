%---------------------------------------------------------------------------------------------------------
%
%  Convert Discourse Representation Structures to Standard Form of First-Order Predicate Logic
% 
%  N. E. Fuchs
%  University of Zurich
%
%  11 October 2022
%
%---------------------------------------------------------------------------------------------------------
%
%  Technical Details
%
%  drs_to_fol(+DRS, +Wrapper, +World, ?FOL) converts a discourse representation structure DRS to its equivalent   
%  first-order formula FOL with possible worlds semantics, and wraps the sentence indices of atomic conditions
%  with Wrapper; token indices of atomic conditions are dropped
%
%  syntax of DRS: negation '-', disjunction 'v', conjunction ',', implication '=>', negation as failure '~',
%  possibility 'can', necessity 'must', label ':', admission 'may', recommendation 'should'; discourse 
%  referents are lists of existentially - or in preconditions of implications universally - quantified variables;
%
%  syntax of FOL: negation '-', disjunction 'v', conjunction '&', implication '=>', universal quantification
%  'forall(X,Formula)', existential quantification 'exists(X,Formula)', where 'X' is a Prolog variable
%
%  based on drs2fol.pl (P. Blackburn & J. Bos, From DRSs to First-Order Logic, 1999) and on Johan Bos, 
%  Computational Semantics in Discourse: Underspecification, Resolution, and Inference, Journal of Logic, 
%  Language and Information 13: 139–157, 2004
%
%  deviating from standard DRT, disjuncts are not translated independently, but similarly to implications to 
%  allow for anaphoric references to precedings disjuncts permitted in ACE (e.g. "A man waits or he sleeps.") 
%
%  proper names occurring as arguments are made explicit objects
%
%  extended to handle the quantifiers 'less than', 'at most' and 'exactly'; DRS conditions derived from 
%  phrases containing these quantifiers are represented as lists; 'less than' is replaced by the negation of
%  'greater than or equal'and 'at most' by the negation of 'greater than'; users must replace 'exactly' by the
%  combination of 'at most' and 'at least'
%
%  negation as failure (NAF) is transformed in a form that can be processed in the following steps
%
%  negation as failure and logical negation cannot be nested into each other
%
%  modal operators (can, must, sentence subordination) are processed using possible world semantics, while 
%  the remaining modal operators (may, should) are flagged as being outside of FOL
%
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
%  declarations
%
%---------------------------------------------------------------------------------------------------------

% module definition and exported predicates
:- module(drs_to_fol, [drs_to_fol/4]).

% RACE modules
:- use_module(support).
:- use_module(race_error_logger).

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

%---------------------------------------------------------------------------------------------------------
%
%  drs_to_fol(+DRS, +Wrapper, +World, -Formula)
%
%  converts discourse representation structure DRS to first-order Formula starting in World, and wraps the
%  sentence indices of atomic conditions with Wrapper; World is prefixed to the arguments of each condition
%
%---------------------------------------------------------------------------------------------------------

drs_to_fol(DRS, Wrapper, World, Formula) :-
  make_proper_names_explicit(DRS, DRS1),
  !,
  drs_to_fol1(DRS1, Wrapper, World, Formula).
  
drs_to_fol1(DRS1, Wrapper, World, Formula) :-  
  replace_all_lists(DRS1, DRS2),
  !,
  drs_to_fol2(DRS2, Wrapper, World, Formula).

drs_to_fol2(DRS2, Wrapper, World, Formula) :- 
  (
    % DRS2 contains negation as failure
    subterm(~(drs(_NAFReferents, _NAFConditions)), DRS2)
    ->
    % replace all variables by constant terms to preserve the integrity of DRS2
    numbervars(DRS2, 1, End),
    transform_negation_as_failure(DRS2, NAFDRS2),
    Limit is End-1,
    % get a new consistent set of variables
    recover_variables(NAFDRS2, Limit, DRS3),
    !,
    drs_to_fol3(DRS3, Wrapper, World, Formula)
  ;
    % DRS2 does not contain negation as failure
    drs_to_fol3(DRS2, Wrapper, World, Formula)
  ). 

drs_to_fol3(drs([],[Condition]), Wrapper, World, Formula) :-
  !,
  cond_to_fol(Condition, Wrapper, World, Formula).

drs_to_fol3(drs([],[Condition1,Condition2|Conditions]), Wrapper, World, Formula1 & Formula2) :-
  !,
  cond_to_fol(Condition1, Wrapper, World, Formula1),
  drs_to_fol3(drs([],[Condition2|Conditions]), Wrapper, World, Formula2).

drs_to_fol3(drs([X|Referents],Conditions), Wrapper, World, exists(X,Formula)) :-
  !,
  drs_to_fol3(drs(Referents,Conditions), Wrapper, World, Formula).

cond_to_fol(-DRS, Wrapper, World, -Formula) :-
  !,
  drs_to_fol3(DRS, Wrapper, World, Formula).

cond_to_fol(question(DRS), Wrapper, World, Formula) :-
  !,
  drs_to_fol1(DRS, Wrapper, World, Formula).

cond_to_fol(command(DRS), Wrapper, World, Formula) :-
  !,
  drs_to_fol1(DRS, Wrapper, World, Formula).

cond_to_fol(DRS1 v DRS2, Wrapper, World, Formula) :-
  (
    % there are anaphoric references from DRS2 to DRS1, i.e.
    % there are variables in DRS2 that occur in DRS1
    term_variables(DRS1, VarsDRS1),
    term_variables(DRS2, VarsDRS2),
    member(X, VarsDRS2), variable_membercheck(X, VarsDRS1)
    ->
    cond_to_fol_disjunct(DRS1 v DRS2, Wrapper, World, Formula)
  ;
    % there are no anaphoric references from DRS2 to DRS1
    drs_to_fol1(DRS1, Wrapper, World, Formula1),
    drs_to_fol1(DRS2, Wrapper, World, Formula2),
    Formula = Formula1 v Formula2
  ).

cond_to_fol_disjunct(drs([],Conditions) v DRS2, Wrapper, World, Formula1 v Formula2) :-
  !,
  drs_to_fol3(drs([],Conditions), Wrapper, World, Formula1),
  drs_to_fol3(DRS2, Wrapper, World, Formula2).

cond_to_fol_disjunct(drs([X|Referents],Conditions) v DRS2, Wrapper, World, exists(X,Formula)) :-
  !,
  cond_to_fol_disjunct(drs(Referents,Conditions) v DRS2, Wrapper, World, Formula).

cond_to_fol(drs([],Conditions) => DRS2, Wrapper, World, Formula1 => Formula2) :-
  !,
  drs_to_fol3(drs([],Conditions), Wrapper, World, Formula1),
  drs_to_fol3(DRS2, Wrapper, World, Formula2).

cond_to_fol(drs([X|Referents],Conditions) => DRS2, Wrapper, World, forall(X,Formula)) :-
  !,
  cond_to_fol(drs(Referents,Conditions) => DRS2, Wrapper, World, Formula).

cond_to_fol(can(DRS), Wrapper, World1, exists(World2, (accessibility_relation(World1,World2) - WrappedIndex) & Formula)) :-
  !,
  WrappedIndex =.. [Wrapper, accessibility_relation],
  drs_to_fol1(DRS, Wrapper, World2, Formula).

cond_to_fol(must(DRS), Wrapper, World1, forall(World2, (accessibility_relation(World1,World2) - WrappedIndex) => Formula)) :-
  !,
  WrappedIndex =.. [Wrapper, accessibility_relation],
  drs_to_fol1(DRS, Wrapper, World2, Formula).

/*
% 28 May 2023: deactivated the hack to avoid confusion using the non-standard modalities obligation and permission
% 25 December 2015: hack to allow for the deontic modalities obligation and permission
% in grammar.functionwords.plp the following substitions were temporarily made
% [recommendation,'it is recommended'] temporarily replaced by [obligation,'it is obligatory'] but auxiliary verb "should" left unchanged
% [admissibility,'it is admissible'] temporarily replaced by [permission,'it is permitted'] but auxiliary verb "may" left unchanged
% thus here obligation occurs as "should" and permission as "may"

cond_to_fol(may(DRS), Wrapper, World1, exists(World2, (accessibility_relation(World1,World2) - WrappedIndex) & Formula)) :-
  !,
  WrappedIndex =.. [Wrapper, accessibility_relation],
  drs_to_fol1(DRS, Wrapper, World2, Formula).

cond_to_fol(should(DRS), Wrapper, World1, forall(World2, (accessibility_relation(World1,World2) - WrappedIndex) => Formula)) :-
  !,
  WrappedIndex =.. [Wrapper, accessibility_relation],
  drs_to_fol1(DRS, Wrapper, World2, Formula).
% end hack
*/

cond_to_fol(World2:DRS, Wrapper, World1, (accessibility_relation(World1,World2) - WrappedIndex) & Formula) :-
  !,
  WrappedIndex =.. [Wrapper, accessibility_relation],
  drs_to_fol1(DRS, Wrapper, World2, Formula).

cond_to_fol(BasicCondition - Index/_, Wrapper, World, NewBasicCondition - WrappedIndex) :-
  % add World argument to BasicCondition
  % for common nouns map operator "eq" to operator "geq", i.e. interpret noun phrase "Count Noun" as "at least Count Noun"
  (
    % BasicCondition is a NAF condition
    BasicCondition =.. [naf, NAFList]
    ->
    add_world_argument_to_NAFList(NAFList, World, NAFListWorld),
    map_eq_geq_NAFList(NAFListWorld, NAFList_eq_geq),
    NewBasicCondition =.. [naf, NAFList_eq_geq]
  ;
    % BasicCondition is a simple condition
    BasicCondition =.. [Functor|Arguments]
    ->
    IntermediateBasicCondition =.. [Functor|[World|Arguments]],
    map_eq_geq(IntermediateBasicCondition, NewBasicCondition) 
  ),
  WrappedIndex =.. [Wrapper, Index].

cond_to_fol(Input, _Wrapper, _World, _Formula) :-
  (Input = may(_DRS) ; Input = should(_DRS)),
  !,
  race_error_logger:add_error_message(race, '', 'Input contains an ACE construct (may, should) outside the scope of RACE.', 'Correct input.'),
  throw(scope).


add_world_argument_to_NAFList(NAFList, World, NewNAFList) :-
  add_world_argument_to_NAFList(NAFList, World, [], NewNAFList).
  
add_world_argument_to_NAFList([], _World, NewNAFList, NewNAFList).

add_world_argument_to_NAFList([Element|RestNAFList], World, SoFar, NewNAFList) :-
  Element =.. [Functor|Arguments],
  NewElement =.. [Functor|[World|Arguments]],
  add_world_argument_to_NAFList(RestNAFList, World, [NewElement|SoFar], NewNAFList).
 
  
map_eq_geq(ConditionIn, ConditionOut) :-
   (
     ConditionIn = object(World, Referent, Noun, Quantity, Unit, eq, Count),
     % do not apply this change to proper names
     \+ Quantity = named, 
     % do not apply this change to the synthetic nouns introduced for distributive and conjunctive plurals
     \+ Noun = na
     ->
     ConditionOut = object(World, Referent, Noun, Quantity, Unit, geq, Count) 
     %%%, race_error_logger:add_warning_message_once(race, '', 'Note that RACE interprets a common noun phrase "Count Noun" as "at least Count Noun".', 'For an alternative interpretation of "Count Noun" use "exactly Count Noun".')
   ;
     ConditionOut = ConditionIn
   ).


map_eq_geq_NAFList(NAFList, NewNAFList) :-
  map_eq_geq_NAFList(NAFList, [], NewNAFList).
  
map_eq_geq_NAFList([], NewNAFList, NewNAFList).

map_eq_geq_NAFList([Element|RestNAFList], SoFar, NewNAFList) :-
  map_eq_geq(Element, NewElement),
  map_eq_geq_NAFList(RestNAFList, [NewElement|SoFar], NewNAFList).

%---------------------------------------------------------------------------------------------------------
%
%  make_proper_names_explicit(DRS, NewDRS)
%
%  NewDRS is DRS in which all terms named(ProperName) are replaced by a new variable NewVariable that is 
%  added to the referents of DRS; conditions object(NewVariable, ProperName, named, na, eq, 1)- 0/_
%  are added to the conditions of DRS
%
%  note that the artificially introduced sentence index 0 is skipped by convert_indices_to_sentences/5 in
%  the module race
%
%---------------------------------------------------------------------------------------------------------

make_proper_names_explicit(drs(Referents, Conditions), NewDRS) :-
  (
    % there are proper names
    setof(ProperName, (support:subterm(named(ProperName), Conditions), nonvar(ProperName)), AllProperNames)
    ->
    modify_names_in_DRS(AllProperNames, drs(Referents, Conditions), NewDRS)
  ;
    % there are no proper names
    NewDRS = drs(Referents, Conditions)
  ).
  
modify_names_in_DRS([], NewDRS, NewDRS).

modify_names_in_DRS([ProperName|ProperNames], drs(Referents, Conditions), NewDRS) :-
  substitute(named(ProperName), NewVariable, Conditions, NewConditions),
  modify_names_in_DRS(ProperNames, drs([NewVariable|Referents], [object(NewVariable, ProperName, named, na, eq, 1)-0/_|NewConditions]), NewDRS).


%---------------------------------------------------------------------------------------------------------
%
%  replace_all_lists(+DRS, -DRSWithoutLists)
%  replace_lists_in_one_DRS(+DRS, -DRSWithoutLists)
%
%  DRSWithoutLists is DRS with all lists derived from the quantifiers 'less than', 'at most', 'exactly'
%  replaced by normal conditions, concretely
%
%  – "less than N" is treated as negation of "at least N"
%  – "at most N" is treated as the negation of "more than N"
%  – "exactly N" is interpreted as itself
%
%  anaphoric references outside of the lists are taken into account
%
%  temporary restrictions:
%
%  – these quantifiers cannot occur in negated phrase, i.e. cases like "John does not have less than 4 cars."
%    have to be expressed positively as "John has at least 4 cars."
%  – no embedding of these quantifiers, i.e. cases like "There are at most 3 cars that have less than 4 
%    wheels." have to be expressed as "There are at most 3 cars. They have less than 4 wheels."
%  – no conjunctive plurals involving these quantifiers, i.e. cases like "There are at most 3 cars and less 
%    than 4 wheels." have to be expressed as "There are at most 3 cars and there are less than 4 wheels."
%  – no distributive plurals involving these quantifiers, i.e. cases like "John has each of at most 3 cars." 
%    have to be expressed as "There are at most 3 cars. John has each of them."
%
%---------------------------------------------------------------------------------------------------------

replace_all_lists(drs(Referents, Conditions), DRSWithoutLists) :-
  (
    % lists in negation
    % example: check_consistency('It is false that there are at most 3 men.', [raw], M, T, P).
    select(-NegatedDRS, Conditions, _RestConditions),
    NegatedDRS = drs(_ReferentsOfNegatedDRS, ConditionsOfNegatedDRS),
    member(List, ConditionsOfNegatedDRS),
    is_list(List)
    ->
    race_error_logger:add_error_message(race, '', 'Current restriction: The quantifiers "less than", "at most", "exactly" cannot occur in a negated phrase.', 'Replace the negated phrase by a positive one.'),
    throw('restriction: negation')
  ;
    % lists in implication
    % example: check_consistency('If there are less than 3 men then there are less than 3 humans.', [raw], M, T, P).
    select(DRS1 => DRS2, Conditions, RestConditions),
    DRS1 = drs(_ReferentsOfDRS1, ConditionsOfDRS1),
    DRS2 = drs(_ReferentsOfDRS2, ConditionsOfDRS2),
    (member(List, ConditionsOfDRS1) ; member(List, ConditionsOfDRS2)),
    is_list(List)
    ->
    replace_lists_in_one_DRS(DRS1, DRS1WithoutLists),
    replace_lists_in_one_DRS(DRS2, DRS2WithoutLists),
    replace_all_lists(drs(Referents, [DRS1WithoutLists => DRS2WithoutLists|RestConditions]), DRSWithoutLists)
  ;
    % lists in disjunction
    % example: check_consistency('There are less than 3 cats or there are at most 3 dogs.', [raw], M, T, P).
    select(DRS1 v DRS2, Conditions, RestConditions),
    DRS1 = drs(_ReferentsOfDRS1, ConditionsOfDRS1),
    DRS2 = drs(_ReferentsOfDRS2, ConditionsOfDRS2),
    (member(List, ConditionsOfDRS1) ; member(List, ConditionsOfDRS2)),
    is_list(List)
    ->
    replace_lists_in_one_DRS(DRS1, DRS1WithoutLists),
    replace_lists_in_one_DRS(DRS2, DRS2WithoutLists),
    replace_all_lists(drs(Referents, [DRS1WithoutLists v DRS2WithoutLists|RestConditions]), DRSWithoutLists)
  ;
    % list as simple condition
    % example: check_consistency('There are less than 3 black cats.', [raw], M, T, P).
    replace_lists_in_one_DRS(drs(Referents, Conditions), DRSWithoutLists)
  ;
    % no lists
    DRSWithoutLists = drs(Referents, Conditions)
  ).

replace_lists_in_one_DRS(drs(Referents, Conditions), drs(NewReferents, NewConditions)) :-
  (
    % there are lists
    select(List, Conditions, RestConditions),
    is_list(List),
    % check for restrictions
    (
      % embedded lists, i.e. more than one quantifier "less than", "at most", "exactly" in a noun phrase
      member(EmbeddedList, List),
      is_list(EmbeddedList)
      ->
      race_error_logger:add_error_message(race, '', 'Current restriction: A noun phrase cannot contain more than one of the quantifiers "less than", "at most", "exactly".', 'Split the noun phrase and combine the elements using anaphoric references.'),
      throw('restriction: nested quantifiers')
    ;
      % conjunctive plurals involving the quantifiers "less than", "at most", "exactly"
      member(has_part(_, _)-_, List)
      ->
      race_error_logger:add_error_message(race, '', 'Current restriction: The quantifiers "less than", "at most", "exactly" cannot occur in conjunctive plurals.', 'Replace the conjunctive plural by a conjunction of verb phrases.'),
      throw('restriction: conjunctive plural')
    ;
      % distributive plural in list
      numbervars(List, 1, _N), support:subterm(has_part(_, _)-_Index, List)
      ->
      race_error_logger:add_error_message(race, '', 'Current restriction: The quantifiers "less than", "at most", "exactly" cannot occur in a distributive plural.', 'Replace the distributive plural "each of less than/at most/exactly Count Noun" by "There are less than/at most/exactly Count Noun. Each of them ..."'),
      throw('restriction: distributive plural')
    ;
      % no restriction
      true
    )
    ->
    (
      % 'exactly'
      selectchk(object(Referent, Noun, Quantity, Unit, exactly, Count)-Index, List, RestList)
      ->
      % 'exactly N' implies only 'exactly N'
      race_error_logger:add_warning_message_once(race, '', 'Note that "exactly N" implies only "exactly N". For more liberal deductions replace "exactly N" by its logical equivalent "at least N" & "at most N".', ''),
      append([object(Referent, Noun, Quantity, Unit, exactly, Count)-Index|RestList], RestConditions, IntermediateConditions), 
      % call replace_lists_in_one_DRS recursively
      replace_lists_in_one_DRS(drs(Referents, IntermediateConditions), drs(NewReferents, NewConditions))
    ;
      % 'less than', 'at most'
      select(object(Referent, Noun, Quantity, Unit, Operator, Count)-Index, List, RestList),
      inverse_of_operator(Operator, InverseOperator),
      (
        % anaphoric references to Referent in RestConditions
        term_variables(RestConditions, VariablesOfRestConditions),
        \+ VariablesOfRestConditions = [],
        term_variables(List, VariablesOfList),
        delete_all_occurrences_of_all_discourse_referents(VariablesOfList, VariablesOfRestConditions, ReferentsOfNegatedInverseOperator),
        delete_all_occurrences_of_all_discourse_referents(Referents, ReferentsOfNegatedInverseOperator, IntermediateReferents)
        -> 
        % negate inverse operator
        IntermediateConditions = [-drs(ReferentsOfNegatedInverseOperator, [object(Referent, Noun, Quantity, Unit, InverseOperator, Count)-Index|RestList]) | RestConditions],
        % check for more lists
        replace_lists_in_one_DRS(drs(IntermediateReferents, IntermediateConditions), drs(NewReferents, NewConditions))
      ;
        % no anaphoric references to Referent in RestConditions
        % delete ReferentsOfList from Referents leaving IntermediateReferents
        term_variables(List, ReferentsOfList),
        delete_all_occurrences_of_all_discourse_referents(Referents, ReferentsOfList, IntermediateReferents),
        % negate inverse operator
        IntermediateConditions = [-drs(ReferentsOfList, [object(Referent, Noun, Quantity, Unit, InverseOperator, Count)-Index | RestList]) | RestConditions],
        % check for more lists
        replace_lists_in_one_DRS(drs(IntermediateReferents, IntermediateConditions), drs(NewReferents, NewConditions))
      )
    )
  ;
    % no lists
    NewReferents = Referents,
    NewConditions = Conditions
  ).
  
inverse_of_operator(less, geq).
inverse_of_operator(leq, greater).
  
  
%-----------------------------------------------------------------------------------------------------------------------------------------------------------------
%
%  transform_negation_as_failure(+DRSIn, -DRSOut) 
%
%    Note: Negation as failure (weak negation) can meaningfully only occur in the precondition of an if-then sentence.
%
%    Restriction: Negation as failure cannot be nested in logical negation, and vice versa.
%
%    DRSIn contains a term ~(NAF-Index) or a conjunct ~(NAF1-Index, NAF2-Index, ...) in the precondition of an implication,
%    DRSOut contains instead naf([NAF1, NAF2, ...])-Index in the same precondition
%
%    The replacement of the conjunct ~(NAF1-Index, NAF2-Index, ...) by the term naf([NAF1, NAF2, ...])-Index keeps the changes of drs_to_fol/4 local
%    and requires no changes of fol_to_clauses/2. However, satchmo/3 had to be extended.
%
%
%  recover_variables(+DRSIn, +Value, -DRSOut)
%
%    Before the execution of transform_negation_as_failure/2 all variables of the input DRS are replaced by constant terms $VAR(N) to keep its integrity. 
%    In recover_variables/3 the terms $VAR(N) are replaced consistently by variables. The parameter 'Value' is the number of replacements necessary.
%
%-----------------------------------------------------------------------------------------------------------------------------------------------------------------
 
transform_negation_as_failure(DRSIn, DRSOut) :-
 (
    DRSIn = drs(Referents, Conditions),
    % DRSIn contains NAF terms
    subterm(~(drs(NAFReferents, NAFConditions)), Conditions)
    ->
    (
      % NAF occurs in the precondition of an implication
      select(drs(PreConditionReferents, PreConditions) => Consequence, Conditions, RestConditions),
      subterm(~(drs(NAFReferents, NAFConditions)), PreConditions)
      ->
      (
        % NAF is nested in logical negation
        subterm(-(drs(_NegReferents, NegConditions)), PreConditions),
        subterm(~(drs(NAFReferents, NAFConditions)), NegConditions)
        ->
        add_error_message_once(race, '', 'Negation as failure cannot be nested in logical negation.', 'Replace "... it is false that it is not provable that P ..." by the semantically equivalent "... P ...".'),
        % though this is a fatal error allow for further processing by converting the NAF DRS into a negated DRS
        substitute(~(drs(NAFReferents, NAFConditions)), -(drs(NAFReferents, NAFConditions)), Conditions, NewConditions),
        DRSOut = drs(Referents, NewConditions)
      ;
        % NAF contains logical negation
        subterm(~(drs(NAFReferents, NAFConditions)), PreConditions),
        subterm(-(drs(_NegReferents, _NegConditions)), NAFConditions)
        ->
        add_error_message_once(race, '', 'Logical negation cannot be nested in negation as failure.', 'Replace the verb in the logical negation by a non-negated verb that has the opposite meaning of the original verb.'),
        % though this is a fatal error allow for further processing by converting the NAF DRS into a negated DRS
        substitute(~(drs(NAFReferents, NAFConditions)), -(drs(NAFReferents, NAFConditions)), Conditions, NewConditions),
        DRSOut = drs(Referents, NewConditions)
      ;
       % NAF is not nested in logical negation and logical negation is not nested in NAF
        append(PreConditionReferents, NAFReferents, NewPreConditionReferents),
        once(subterm(_NAFCondition-Index, NAFConditions)),
        % collect NAFConditions
        findall(NAFCondition, subterm(NAFCondition - _Index, NAFConditions), AllNAFConditions),
        substitute(~(drs(NAFReferents, NAFConditions)), naf(AllNAFConditions)-Index, PreConditions, NewPreConditions),
        append(RestConditions, [drs(NewPreConditionReferents, NewPreConditions) => Consequence], NewConditions),
        transform_negation_as_failure(drs(Referents, NewConditions), DRSOut) 
      )
    ;
      % negation as failure does not occur in the precondition of an implication
      add_error_message_once(race, '', 'Note that negation as failure can meaningfully only be used in the if-part of an if-then sentence.', ''),
      % though this is a fatal error allow for further processing by converting the NAF DRS into a negated DRS
      substitute(~(drs(NAFReferents, NAFConditions)), -(drs(NAFReferents, NAFConditions)), Conditions, NewConditions),
      DRSOut = drs(Referents, NewConditions)
    )
  ;
    % no (further) NAF terms
    DRSOut = DRSIn
  ).
     
  
recover_variables(DRSOut, 0, DRSOut).

recover_variables(DRSIn, Value, DRSOut) :-
  support:substitute('$VAR'(Value), _X, DRSIn, DRSIntermediate),
  NextValue is Value - 1,
  recover_variables(DRSIntermediate, NextValue, DRSOut).
   
  
%-----------------------------------------------------------------------------------------------------------------------------------------------------------------
%
%  delete_all_occurrences_of_all_discourse_referents(+ReferentsIn, +ReferentsToDelete, -ReferentsOut)
%
%    - ReferentsOut is the list ReferentsIn without all occurrences of the elements of the list ReferentsToDelete
%
%
%  delete_all_occurrences_of_one_discourse_referent(+ReferentsIn, +ReferentToDelete, -ReferentsOut)
%
%    - ReferentsOut is the list ReferentsIn without all occurrences of ReferentToDelete
%
%-----------------------------------------------------------------------------------------------------------------------------------------------------------------

delete_all_occurrences_of_all_discourse_referents(Referents, [], Referents) :-
  !.

delete_all_occurrences_of_all_discourse_referents(ReferentsIn, [ReferentToDelete|ReferentsToDelete], ReferentsOut) :-
  delete_all_occurrences_of_one_discourse_referent(ReferentsIn, ReferentToDelete, ReferentsIM),
  delete_all_occurrences_of_all_discourse_referents(ReferentsIM, ReferentsToDelete, ReferentsOut).


delete_all_occurrences_of_one_discourse_referent([], _ReferentToDelete, []).

delete_all_occurrences_of_one_discourse_referent([Referent|Referents], ReferentToDelete, ReferentsOut) :-
  (
    Referent == ReferentToDelete
    -> 
    delete_all_occurrences_of_one_discourse_referent(Referents, ReferentToDelete, ReferentsOut)
  ;
    delete_all_occurrences_of_one_discourse_referent(Referents, ReferentToDelete, ReferentsRest),
    ReferentsOut = [Referent|ReferentsRest]
  ).


%---------------------------------------------------------------------------------------------------------