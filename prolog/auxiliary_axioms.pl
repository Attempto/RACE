%---------------------------------------------------------------------------------------------------------
%
%  Auxiliary FOL and Prolog Axioms for the Attempto Reasoner RACE
% 
%  N. E. Fuchs
%  University of Zurich
%  
%  14 July 2025 (added test cade for distinct_derived_noun_phrases)
%
%---------------------------------------------------------------------------------------------------------
%
%  Technical Details
%
%  This module contains FOL and Prolog auxiliary axioms that express domain-independent knowledge like
%  meaning postulates, relations between plurals and singulars, features of natural numbers etc. 
%
%  FOL axioms are translated into Satchmo clauses, and are – like Satchmo clauses derived from ACE axioms 
%  and theorems – executed by forward reasoning. Prolog axioms are Prolog clauses executed by backward 
%  reasoning. 
%
%  This means that every FOL axiom contributes to the cyclic process of the Satchmo interpreter, and 
%  is executed if the preconditions of its body are fulfilled - whether or not its head is needed for
%  further reasoning. Prolog axioms, however, are only executed if their heads are required. 
%
%  Some FOL axioms can also be expressed as Prolog axioms. In this case and if backward reasoning makes 
%  sense, Prolog axioms are preferred since they are more efficient.
%
%  Furthermore, Prolog auxiliary axioms can use built-in and non-logical Prolog predicates.
%
%  syntax of Prolog axioms:
%  prolog_axiom_text(AxiomID, Text)
%  prolog_axiom(Condition, IndicesSoFar, [prolog_axiom(AxiomID)|Indices])
%  where AxiomID is an atom, Text is a string, Condition is the DRS condition to be proved, IndicesSoFar is
%  a list of indices of axioms used so far in the proof of the respective head or body of a Satchmo clause,
%  and Indices are the indices of axioms used to prove Condition; IndicesSoFar can be used to ensure that
%  only one of two exclusive auxiliary axioms is used
%
%  syntax of FOL axioms: 
%  fol_axiom(AxiomID, Formula, Text)
%  where AxiomID is an atom, Formula is a FOL formula, and Text is a string
%
%  syntax of FOL formulas: negation '-', conjunction '&', disjunction 'v', implication '=>', universal 
%  quantification 'forall(X, Formula)', existential quantification 'exists(X, Formula)'; in FOL axioms nested  
%  universal quantifiers or nested existential quantifiers can alternatively be written using quantifier 
%  lists, e.g. 'forall(X, forall(Y, exists(U, exists(V, Formula))))' as 'forall([X,Y], exists([U,V],Formula))'
%
%---------------------------------------------------------------------------------------------------------
%
%  Log
%
%  2 November 2008: made disjunctions in  axioms c5 - c15 determninate; does this prevent some solutions?
%
%  5 March 2025: terminated development of the query "What is entailed?" since the approach chosen 
%  cannot be extended to handle negation
%
%  14 July 2025: added test cade for distinct_derived_noun_phrases
%
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
%  To Do
%
%  consider treating be_ID and be_NP (and be_ADJ?) together to reduce the number of auxiliary axioms and
%  thus eliminate choice points
%
%  check deactivated code
%
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
%  declarations
%
%---------------------------------------------------------------------------------------------------------

% module definition and exported predicates
:- module(auxiliary_axioms, [prolog_axiom/3, prolog_axiom_text/2, fol_axiom/3]).

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

% RACE modules
:- use_module(satchmo).
:- use_module(race_error_logger).
:- use_module(support).
:- use_module(library(clpr)).
:- use_module('../ape/utils/drs_to_ace', [drs_to_ace/2]).

% local dynamic predicates
:- dynamic([prolog_axiom/3, prolog_axiom_text/2, fol_axiom/3]).

%---------------------------------------------------------------------------------------------------------
%
%  Prolog 
%
%  Example Prolog programs that are called via calls of the form [Name, Arguments, Results]
%
%--------------------------------------------------------------------------------------------------------

% Euclid's algorithm for the greatest common divisor
gcd(X,Y,GCD) :-
  (
    X=Y
    ->
    GCD = X
  ;
    X > Y
    ->
    X1 is X - Y,
    gcd(X1,Y,GCD)
  ;
    X < Y
    ->
    Y1 is Y - X,
    gcd(X,Y1,GCD)
  ).  
  
  
% simple recursion 
% example: A number is 1. If there is a number N then a number N1 is N+1. |- A number is 3.
simple_recursion(Start, Goal) :-
  (
    Start = Goal
    ->
    true
  ;
    Start1 is Start+1,
    simple_recursion(Start1, Goal)
  ).

  
%---------------------------------------------------------------------------------------------------------
%
%  frame axioms
%
%  If a situation holds at an initial time and it is not provable that the situation does not hold at a 
%  later time then the situation holds at the later time.
%
%  restrictions: "hold" is an intransitive verb – including the copula – or is a copula plus adjective  
%  or is a transitive verb or is a ditransitive verb
%
%---------------------------------------------------------------------------------------------------------

% intransitive verbs
% If something X "verbs" at a time T1 and there is a time T2 and T2 > T1 and it is not provable that X does not "verb" at the time T2 then X "verbs" at the time T2.
% example 1: A man sleeps at an initial time T1. There is a later time T2 and T2 > T1. |- A man sleeps at a later time.
% example 2: If somebody X falls asleep at a time T then X sleeps at T. John falls asleep at a time T1. There is a later time T2 and T2 > T1. |- John sleeps at a later time.
% example 3: A fact exists at a time T1. If a fact exists at a time T then John does not sleep at T. There is a later time T2 and T2 > T1. |- There is a later time. John does not sleep at the later time.
% counter example 1: A man sleeps at an initial time T1. There is a later time T2 and T2 > T1. The man does not sleep at the later time. |/– A man sleeps at a later time.
% comment to inversion: Since the theorem contains "later time" in a negated context, "later time" has to be introduced before in a positive context.
% inversion of counter example 1: A man sleeps at an initial time T1. There is a later time T2 and T2 > T1. The man does not sleep at the later time. |- There is a later time. A man does not sleep at the later time.
% counter example 2: A man sleeps at a time T1. There is a later time T2 and T2 > T1. If an alarm rings at a time T then the man does not sleep at the time T. An alarm rings at the time T2. |/– A man sleeps at a later time.
% inversion of counter example 2: A man sleeps at a time T1. There is a later time T2 and T2 > T1. If an alarm rings at a time T then the man does not sleep at the time T. An alarm rings at the time T2.|- There is a later time. A man does not sleep at the later time.
% example 4: A man is in a house at a time T1. There is a later time T2 and T2 > T1.  If the man leaves the house at a time T then the man is not in the house at the time T. The man leaves the house at the time T2. |- There is a later time. There is a house. A man is not in the house at the later time.
prolog_axiom_text(frame1, 'Frame Axiom 1: Persistence of intransitive verb.').
prolog_axiom(predicate(World, _Ref, Verb, Item), _IndicesSoFar, [prolog_axiom(frame1)|Indices]) :-
  % use this axiom only for proofs, not for consistency checking
  nb_getval(global_parameters, Parameters),
  memberchk(prove, Parameters),
  user:clauses(Clauses),
  exists_asserted_atom(predicate(World, RefVerb, Verb, Item), Indices1), 
  exists_asserted_atom(modifier_pp(World, RefVerb, at, T1), Indices2), 
  exists_asserted_atom(object(World, Item, _Noun, _, _, _, _), Indices3),
  exists_asserted_atom(object(World, T1, time, countable, na, geq, 1), Indices4), 
  exists_asserted_atom(object(World, T2, time, countable, na, geq, 1), Indices5), 
  % establish the temporal order if there are sequences of times, like T1,T2,T3 with T2 > T1, T3 > T2, so that T3 > T1
  temporal_order(T1, T2, Indices6),
  % counter example 1
  \+ member(satchmo_clause((predicate(World, RefVerbNAF, Verb, Item), modifier_pp(World, RefVerbNAF, at, T2)), fail, _), Clauses),
  % counter example 2  
  \+ (
       member(satchmo_clause(true, Head, _), Clauses),
       conjunction_to_list(Head, HeadAsList),
       member(modifier_pp(World, _, at, T2), HeadAsList),
       member(satchmo_clause(Body, fail, [axiom(_)]), Clauses),
       conjunction_to_list(Body, BodyAsList),
       member(predicate(World, RefVerbNAF, Verb, Item), BodyAsList),
       member(modifier_pp(World, RefVerbNAF, at, T2), BodyAsList)
     ),
  append([Indices1,Indices2,Indices3,Indices4,Indices5,Indices6], Indices). 

prolog_axiom(modifier_pp(World, _Ref, at, T2), _IndicesSoFar, [prolog_axiom(frame1)|Indices]) :-
  % use this axiom only for proofs, not for consistency checking
  nb_getval(global_parameters, Parameters),
  memberchk(prove, Parameters),
  user:clauses(Clauses),
  exists_asserted_atom(predicate(World, RefVerb, Verb, Item), Indices1), 
  exists_asserted_atom(modifier_pp(World, RefVerb, at, T1), Indices2), 
  exists_asserted_atom(object(World, Item, _Noun, _, _, _, _), Indices3),
  exists_asserted_atom(object(World, T1, time, countable, na, geq, 1), Indices4), 
  exists_asserted_atom(object(World, T2, time, countable, na, geq, 1), Indices5), 
  % establish the temporal order if there are sequences of times, like T1,T2,T3 with T2 > T1, T3 > T2, so that T3 > T1
  temporal_order(T1, T2, Indices6),
  % counter example 1
  \+ member(satchmo_clause((predicate(World, RefVerbNAF, Verb, Item), modifier_pp(World, RefVerbNAF, at, T2)), fail, _), Clauses),
  % counter example 2
  \+ (
       member(satchmo_clause(true, Head, _), Clauses),
       conjunction_to_list(Head, HeadAsList),
       member(modifier_pp(World, _, at, T2), HeadAsList),
       member(satchmo_clause(Body, fail, [axiom(_)]), Clauses),
       conjunction_to_list(Body, BodyAsList),
       member(predicate(World, RefVerbNAF, Verb, Item), BodyAsList),
       member(modifier_pp(World, RefVerbNAF, at, T2), BodyAsList)
     ),
  append([Indices1,Indices2,Indices3,Indices4,Indices5,Indices6], Indices). 


% copula plus adjective
% If something X is "adjective" at a time T1 and there is a time T2 and T2 > T1 and it is not provable that 
% X is not "adjective" at the time T2 then X is "adjective" at the time T2.
% example: A window is open at an initial time T0. There is a later time T and T > T0. |- A window is open at a later time.
% counter example 1: A window is open at an initial time T1. There is a later time T2 and T > T1. The window is not open at the later time. |/– A window is open at a later time.
% counter example 2: A window is open at an initial time T1. There is a later time T2 and T2 > T1. If somebody closes the window at a time T then the window is not open at T. Somebody closes the window at the time T2. |/– A window is open at a later time.
% comment to inversion: Since the theorem contains "later time" in a negated context, "later time" has to be introduced before in a positive context.
% inversion of counter example 2: A window is open at an initial time T1. There is a later time T2 and T2 > T1. If somebody closes the window at a time T then the window is not open at T. Somebody closes the window at the time T2. |- There is a later time. A window is not open at the later time.
prolog_axiom_text(frame2, 'Frame Axiom 2: Persistence of copula plus adjective.').
prolog_axiom(predicate(World, _Ref1, be_ADJ, Item, _Ref2), _IndicesSoFar, [prolog_axiom(frame2)|Indices]) :-
  % use this axiom only for proofs, not for consistency checking
  nb_getval(global_parameters, Parameters),
  memberchk(prove, Parameters),
  user:clauses(Clauses),
  exists_asserted_atom(predicate(World, RefCopula, be_ADJ, Item, RefAdjective), Indices1),
  exists_asserted_atom(modifier_pp(World, RefCopula, at, T1), Indices2),
  exists_asserted_atom(property(World, RefAdjective, Adjective, pos), Indices3),
  exists_asserted_atom(object(World, Item, _Noun, _, _, _, _), Indices4),
  exists_asserted_atom(object(World, T1, time, countable, na, geq, 1), Indices5),
  exists_asserted_atom(object(World, T2, time, countable, na, geq, 1), Indices6),
  % make sure that T2 is the time intended for inertia indicated by the respective adjective in the theorem
  member(satchmo_clause(Head, _Body, [theorem(_)|_]), Clauses), 
  subterm(object(World, RefTime, time, countable, na, geq, 1), Head), 
  subterm(property(World, RefTime, AdjectiveT2, _), Head),
  (exists_asserted_atom(property(World, T2, AdjectiveT2, pos), _) ; exists_asserted_atom(property(World, T2, AdjectiveT2, comp), _) ; exists_asserted_atom(property(World, T2, AdjectiveT2, sup), _)),
  % establish the temporal order if there are sequences of times, like T1,T2,T3 with T2 > T1, T3 > T2, so that T3 > T1
  temporal_order(T1, T2, Indices7),
  % counter example 1
  \+ member(satchmo_clause((property(World, RefAdjectiveNAF, Adjective, pos), predicate(World, RefCopulaNAF, be_ADJ, Item, RefAdjectiveNAF), modifier_pp(World, RefCopulaNAF, at, T2)), fail, _), Clauses),
  % counter example 2
  \+ (
       member(satchmo_clause(NAFBody, fail, [axiom(_)]), Clauses),
       subterm(property(World, RefAdjectiveNAF, Adjective, pos), NAFBody),
       subterm(predicate(World, RefCopulaNAF, be_ADJ, Item, RefAdjectiveNAF), NAFBody),
       subterm(modifier_pp(World, RefCopulaNAF, at, T2), NAFBody),
       member(satchmo_clause(true, NAFHead, [axiom(_)]), Clauses),
       (subterm(modifier_pp(World, _, at, T1), NAFHead) -> true ; subterm(modifier_pp(World, _, at, T2), NAFHead))
     ),
  append([Indices1,Indices2,Indices3,Indices4,Indices5,Indices6, Indices7], Indices).

prolog_axiom(modifier_pp(World, _Ref1, at, T2), _IndicesSoFar, [prolog_axiom(frame2)|Indices]) :-
  % use this axiom only for proofs, not for consistency checking
  nb_getval(global_parameters, Parameters),
  memberchk(prove, Parameters),
  user:clauses(Clauses),
  exists_asserted_atom(predicate(World, RefCopula, be_ADJ, Item, RefAdjective), Indices1),
  exists_asserted_atom(modifier_pp(World, RefCopula, at, T1), Indices2),
  exists_asserted_atom(property(World, RefAdjective, Adjective, pos), Indices3),
  exists_asserted_atom(object(World, Item, _Noun, _, _, _, _), Indices4),
  exists_asserted_atom(object(World, T1, time, countable, na, geq, 1), Indices5),
  exists_asserted_atom(object(World, T2, time, countable, na, geq, 1), Indices6),
  % make sure that T2 is the time intended for inertia indicated by the respective adjective in the theorem
  member(satchmo_clause(Head, _Body, [theorem(_)|_]), Clauses), 
  subterm(object(World, RefTime, time, countable, na, geq, 1), Head), 
  subterm(property(World, RefTime, AdjectiveT2, _), Head),
  (exists_asserted_atom(property(World, T2, AdjectiveT2, pos), _) ; exists_asserted_atom(property(World, T2, AdjectiveT2, comp), _) ; exists_asserted_atom(property(World, T2, AdjectiveT2, sup), _)),
  % establish the temporal order if there are sequences of times, like T1,T2,T3 with T2 > T1, T3 > T2, so that T3 > T1
  temporal_order(T1, T2, Indices7),
  % counter example 1
  \+ member(satchmo_clause((property(World, RefAdjectiveNAF, Adjective, pos), predicate(World, RefCopulaNAF, be_ADJ, Item, RefAdjectiveNAF), modifier_pp(World, RefCopulaNAF, at, T2)), fail, _), Clauses),
  % counter example 2
  \+ (
       member(satchmo_clause(NAFBody, fail, [axiom(_)]), Clauses),
       subterm(property(World, RefAdjectiveNAF, Adjective, pos), NAFBody),
       subterm(predicate(World, RefCopulaNAF, be_ADJ, Item, RefAdjectiveNAF), NAFBody),
       subterm(modifier_pp(World, RefCopulaNAF, at, T2), NAFBody),
       member(satchmo_clause(true, NAFHead, [axiom(_)]), Clauses),
       (subterm(modifier_pp(World, _, at, T1), NAFHead) -> true ; subterm(modifier_pp(World, _, at, T2), NAFHead))
     ),
  append([Indices1,Indices2,Indices3,Indices4,Indices5,Indices6, Indices7], Indices).

prolog_axiom(property(World, _Ref2, Adjective, pos),  _IndicesSoFar, [prolog_axiom(frame2)|Indices]) :-
  % use this axiom only for proofs, not for consistency checking
  nb_getval(global_parameters, Parameters),
  memberchk(prove, Parameters),
  user:clauses(Clauses),
  exists_asserted_atom(predicate(World, RefCopula, be_ADJ, Item, RefAdjective), Indices1),
  exists_asserted_atom(modifier_pp(World, RefCopula, at, T1), Indices2),
  exists_asserted_atom(property(World, RefAdjective, Adjective, pos), Indices3),
  exists_asserted_atom(object(World, Item, _Noun, _, _, _, _), Indices4),
  exists_asserted_atom(object(World, T1, time, countable, na, geq, 1), Indices5),
  exists_asserted_atom(object(World, T2, time, countable, na, geq, 1), Indices6),
  % make sure that T2 is the time intended for inertia indicated by the respective adjective in the theorem
  member(satchmo_clause(Head, _Body, [theorem(_)|_]), Clauses), 
  subterm(object(World, RefTime, time, countable, na, geq, 1), Head), 
  subterm(property(World, RefTime, AdjectiveT2, _), Head),
  (exists_asserted_atom(property(World, T2, AdjectiveT2, pos), _) ; exists_asserted_atom(property(World, T2, AdjectiveT2, comp), _) ; exists_asserted_atom(property(World, T2, AdjectiveT2, sup), _)),
  % establish the temporal order if there are sequences of times, like T1,T2,T3 with T2 > T1, T3 > T2, so that T3 > T1
  temporal_order(T1, T2, Indices7),
  % counter example 1
  \+ member(satchmo_clause((property(World, RefAdjectiveNAF, Adjective, pos), predicate(World, RefCopulaNAF, be_ADJ, Item, RefAdjectiveNAF), modifier_pp(World, RefCopulaNAF, at, T2)), fail, _), Clauses),
  % counter example 2
  \+ (
       member(satchmo_clause(NAFBody, fail, [axiom(_)]), Clauses),
       subterm(property(World, RefAdjectiveNAF, Adjective, pos), NAFBody),
       subterm(predicate(World, RefCopulaNAF, be_ADJ, Item, RefAdjectiveNAF), NAFBody),
       subterm(modifier_pp(World, RefCopulaNAF, at, T2), NAFBody),
       member(satchmo_clause(true, NAFHead, [axiom(_)]), Clauses),
       (subterm(modifier_pp(World, _, at, T1), NAFHead) -> true ; subterm(modifier_pp(World, _, at, T2), NAFHead))
     ),
  append([Indices1,Indices2,Indices3,Indices4,Indices5,Indices6, Indices7], Indices).


% transitive verbs
% If something X "verbs" something Y at a time T1 and there is a time T2 and T2 > T1 and it is not provable that 
% X does not "verb" Y at the time T2 then X "verbs" Y at the time T2.
% example: A man owns a house at an initial time T1. There is a later time T2 and T2 > T1. |- A man owns a house at a later time.
% counter example 1: A man owns a house at an initial time T1. There is a later time T2 and T2 > T1. The man does not own the house at T2. |/– A man owns a house at a later time.
% counter example 2: A man owns a house at an initial time T1. There is a later time T2 and T2 > T1. If somebody X sells the house at a time T then X does not own the house at T. The man sells the house at the time T2. |/– A man owns a house at a later time.
% comment to inversion: Since the theorem contains "later time" and "house" in a negated context, "later time" and "house" have to be introduced before in a positive context. 
% inversion of counter example 2: A man owns a house at a time T1. There is a later time T2 and T2 > T1. If the man sells the house at a time T then the man does not own the house at T. The man sells the house at the time T2. |- There is a later time. There is a house. A man does not own the house at the later time.
prolog_axiom_text(frame3, 'Frame Axiom 3: Persistence of transitive verb.').
prolog_axiom(predicate(World, RefVerb, Verb, ItemSubject, ItemObject), _IndicesSoFar, [prolog_axiom(frame3)|Indices]) :-
  % use this axiom only for proofs, not for consistency checking
  nb_getval(global_parameters, Parameters),
  memberchk(prove, Parameters),
  user:clauses(Clauses),
  exists_asserted_atom(predicate(World, RefVerb, Verb, ItemSubject, ItemObject), Indices1), 
  exists_asserted_atom(modifier_pp(World, RefVerb, at, T1), Indices2), 
  exists_asserted_atom(object(World, ItemSubject, _Subject, _, _, _, _), Indices3),
  exists_asserted_atom(object(World, ItemObject, _Object, _, _, _, _), Indices4),
  exists_asserted_atom(object(World, T1, time, countable, na, geq, 1), Indices5), 
  exists_asserted_atom(object(World, T2, time, countable, na, geq, 1), Indices6), 
  % establish the temporal order if there are sequences of times, like T1,T2,T3 with T2 > T1, T3 > T2, so that T3 > T1
  temporal_order(T1, T2, Indices7),
  % counter example 1
  \+ member(satchmo_clause((predicate(World, RefVerbNAF, Verb, ItemSubject, ItemObject), modifier_pp(World, RefVerbNAF, at, T2)), fail, _), Clauses),
  % counter example 2  
  \+ (
       member(satchmo_clause(true, Head, _), Clauses),
       conjunction_to_list(Head, HeadAsList),
       member(modifier_pp(World, _, at, T2), HeadAsList),
       member(satchmo_clause(Body, fail, [axiom(_)]), Clauses),
       conjunction_to_list(Body, BodyAsList),
       member(predicate(World, RefVerbNAF, Verb, ItemSubject, ItemObject), BodyAsList),
       member(modifier_pp(World, RefVerbNAF, at, T2), BodyAsList)
     ),
  append([Indices1,Indices2,Indices3,Indices4,Indices5,Indices6, Indices7], Indices).

prolog_axiom(modifier_pp(World, RefVerb, at, T2), _IndicesSoFar, [prolog_axiom(frame3)|Indices]) :-
  % use this axiom only for proofs, not for consistency checking
  nb_getval(global_parameters, Parameters),
  memberchk(prove, Parameters),
  user:clauses(Clauses),
  exists_asserted_atom(predicate(World, RefVerb, Verb, ItemSubject, ItemObject), Indices1), 
  exists_asserted_atom(modifier_pp(World, RefVerb, at, T1), Indices2), 
  exists_asserted_atom(object(World, ItemSubject, _Subject, _, _, _, _), Indices3),
  exists_asserted_atom(object(World, ItemObject, _Object, _, _, _, _), Indices4),
  exists_asserted_atom(object(World, T1, time, countable, na, geq, 1), Indices5), 
  exists_asserted_atom(object(World, T2, time, countable, na, geq, 1), Indices6), 
  % establish the temporal order if there are sequences of times, like T1,T2,T3 with T2 > T1, T3 > T2, so that T3 > T1
  temporal_order(T1, T2, Indices7),
  % counter example 1
  \+ member(satchmo_clause((predicate(World, RefVerbNAF, Verb, ItemSubject, ItemObject), modifier_pp(World, RefVerbNAF, at, T2)), fail, _), Clauses),
  % counter example 2  
  \+ (
       member(satchmo_clause(true, Head, _), Clauses),
       conjunction_to_list(Head, HeadAsList),
       member(modifier_pp(World, _, at, T2), HeadAsList),
       member(satchmo_clause(Body, fail, [axiom(_)]), Clauses),
       conjunction_to_list(Body, BodyAsList),
       member(predicate(World, RefVerbNAF, Verb, ItemSubject, ItemObject), BodyAsList),
       member(modifier_pp(World, RefVerbNAF, at, T2), BodyAsList)
     ),
  append([Indices1,Indices2,Indices3,Indices4,Indices5,Indices6, Indices7], Indices).


% ditransitive verbs
% If something X "verbs" something Y to something Z at a time T1 and there is a time T2 and T2 > T1 and it is not provable that 
% X does not "verb" Y to Z at the time T2 then X "verbs" Y to Z at the time T2.
% example: A man owes a bank a sum at an initial time T1. There is a later time T2 and T2 > T1. |- A man owes a bank a sum at a later time.
% note: The verb "owe" is both transitive and ditransitive. In "A man owes a sum to a bank." APE interprets it as transitive, and not – as intended – as ditransitive.
% counter example 1: A man owes a bank a sum at an initial time T1. There is a later time T2 and T2 > T1. The man does not owe a bank a sum at T2. |/– A man owes a bank a sum at a later time.
% counter example 2: A man owes a bank a sum at an initial time T1. There is a later time T2 and T2 > T1. If somebody X repays the bank the sum at a time T then X does not owe the bank the sum at T. The man repays the bank the sum at the time T2. |/– A man owes a bank a sum at a later time.
% comment to inversion: Since the theorem contains "later time", "bank" and "sum" in a negated context, "later time", "bank" and "sum" have to be introduced before in a positive context. 
% inversion of counter example 2: A man owes a bank a sum at a time T1. There is a later time T2 and T2 > T1. If the man repays the bank the sum at a time T then the man does not owe the bank the sum at T. The man repays the bank the sum at the time T2. |- There is a later time. There is a bank. There is a sum. A man does not owe the bank the sum at the later time.
prolog_axiom_text(frame4, 'Frame Axiom 4: Persistence of ditransitive verb.').
prolog_axiom(predicate(World, RefVerb, Verb, ItemSubject, ItemDirectObject, ItemInDirectObject), _IndicesSoFar, [prolog_axiom(frame4)|Indices]) :-
  % use this axiom only for proofs, not for consistency checking
  nb_getval(global_parameters, Parameters),
  memberchk(prove, Parameters),
  user:clauses(Clauses),
  exists_asserted_atom(predicate(World, RefVerb, Verb, ItemSubject, ItemDirectObject, ItemInDirectObject), Indices1), 
  exists_asserted_atom(modifier_pp(World, RefVerb, at, T1), Indices2), 
  exists_asserted_atom(object(World, ItemSubject, _Subject, _, _, _, _), Indices3),
  exists_asserted_atom(object(World, ItemDirectObject, _DirectObject, _, _, _, _), Indices4),
  exists_asserted_atom(object(World, ItemInDirectObject, _IndirectObject, _, _, _, _), Indices5),
  exists_asserted_atom(object(World, T1, time, countable, na, geq, 1), Indices6), 
  exists_asserted_atom(object(World, T2, time, countable, na, geq, 1), Indices7), 
  % establish the temporal order if there are sequences of times, like T1,T2,T3 with T2 > T1, T3 > T2, so that T3 > T1
  temporal_order(T1, T2, Indices8),
  % counter example 1
  \+ member(satchmo_clause((predicate(World, RefVerbNAF, Verb, ItemSubject, ItemDirectObject, ItemInDirectObject), modifier_pp(World, RefVerbNAF, at, T2)), fail, _), Clauses),
  % counter example 2  
  \+ (
       member(satchmo_clause(true, Head, _), Clauses),
       conjunction_to_list(Head, HeadAsList),
       member(modifier_pp(World, _, at, T2), HeadAsList),
       member(satchmo_clause(Body, fail, [axiom(_)]), Clauses),
       conjunction_to_list(Body, BodyAsList),
       member(predicate(World, RefVerbNAF, Verb, ItemSubject, ItemDirectObject, ItemInDirectObject), BodyAsList),
       member(modifier_pp(World, RefVerbNAF, at, T2), BodyAsList)
     ),
  append([Indices1,Indices2,Indices3,Indices4,Indices5,Indices6, Indices7, Indices8], Indices).

prolog_axiom(modifier_pp(World, RefVerb, at, T2), _IndicesSoFar, [prolog_axiom(frame4)|Indices]) :-
  % use this axiom only for proofs, not for consistency checking
  nb_getval(global_parameters, Parameters),
  memberchk(prove, Parameters),
  user:clauses(Clauses),
  exists_asserted_atom(predicate(World, RefVerb, Verb, ItemSubject, ItemDirectObject, ItemInDirectObject), Indices1), 
  exists_asserted_atom(modifier_pp(World, RefVerb, at, T1), Indices2), 
  exists_asserted_atom(object(World, ItemSubject, _Subject, _, _, _, _), Indices3),
  exists_asserted_atom(object(World, ItemDirectObject, _DirectObject, _, _, _, _), Indices4),
  exists_asserted_atom(object(World, ItemInDirectObject, _IndirectObject, _, _, _, _), Indices5),
  exists_asserted_atom(object(World, T1, time, countable, na, geq, 1), Indices6), 
  exists_asserted_atom(object(World, T2, time, countable, na, geq, 1), Indices7), 
  % establish the temporal order if there are sequences of times, like T1,T2,T3 with T2 > T1, T3 > T2, so that T3 > T1
  temporal_order(T1, T2, Indices8),
  % counter example 1
  \+ member(satchmo_clause((predicate(World, RefVerbNAF, Verb, ItemSubject, ItemDirectObject, ItemInDirectObject), modifier_pp(World, RefVerbNAF, at, T2)), fail, _), Clauses),
  % counter example 2  
  \+ (
       member(satchmo_clause(true, Head, _), Clauses),
       conjunction_to_list(Head, HeadAsList),
       member(modifier_pp(World, _, at, T2), HeadAsList),
       member(satchmo_clause(Body, fail, [axiom(_)]), Clauses),
       conjunction_to_list(Body, BodyAsList),
       member(predicate(World, RefVerbNAF, Verb, ItemSubject, ItemDirectObject, ItemInDirectObject), BodyAsList),
       member(modifier_pp(World, RefVerbNAF, at, T2), BodyAsList)
     ),
  append([Indices1,Indices2,Indices3,Indices4,Indices5,Indices6, Indices7, Indices8], Indices).

/* 
% 23 August 2021: inactivated since it is only needed for the Yale Shooting Problem and ...
% ... causes wrong deductions in other cases, e.g. the sleeping example
% relate fluents to the precondition of an implication
% needed in Yale Shooting Problem
% example 1: A window is open at a time T1. There is a later time T2 and T2 > T1. If a window is open at the later time T2 then "consequence". |- "g"
% example 2: A window is open at a time T1. There is a later time T2 and T2 > T1. There is a final time T3 and T3 > T2. If a window is open at the final time T3 then "consequence". |- "consequence"
prolog_axiom_text(frame5, 'Frame Axiom 5: Fluent used in the precondition of an implication.').
prolog_axiom(modifier_pp(World, RefVerb, at, T2), IndicesSoFar, [prolog_axiom(frame5)|Indices]) :-
  % modifier_pp(World, RefVerb, at, T2) must occur in the precondition of an implicative axiom
  user:clauses(Clauses),
  member(satchmo_clause(Body, Head, [axiom(_)]), Clauses),
  Body \= true, 
  subterm(modifier_pp(World, RefVerb, at, T2), Body),
  % matching modifier with preceding time
  exists_asserted_atom(modifier_pp(World, RefVerb, at, T1), Indices1), 
  temporal_order(T1, T2, Indices2), 
  !,
  append([Indices1,Indices2], Indices).
*/ 

temporal_order(T1, T2, Index) :-
  T1 \== T2,
  (
    (
      exists_asserted_atom(formula(World, T2, >, T1), Index) 
    ; 
      exists_asserted_atom(formula(World, T1, <, T2), Index) 
    ; 
      (exists_asserted_atom(predicate(World, RefVerb, _Verb, T1), Index), exists_asserted_atom(modifier_pp(World, RefVerb, before, T2), Index))
    ; 
      (exists_asserted_atom(predicate(World, RefVerb, _Verb, T2), Index), exists_asserted_atom(modifier_pp(World, RefVerb, after, T1), Index))
    )
    ->
    true
  ;
    (
      exists_asserted_atom(formula(World, T3, >, T1), Index31) 
    ; 
      exists_asserted_atom(formula(World, T1, <, T3), Index31) 
    ; 
      (exists_asserted_atom(predicate(World, RefVerb, _Verb, T1), Index31), exists_asserted_atom(modifier_pp(World, RefVerb, before, T3), Index31))
    ; 
      (exists_asserted_atom(predicate(World, RefVerb, _Verb, T3), Index31), exists_asserted_atom(modifier_pp(World, RefVerb, after, T1), Index31))
    ),
    T3 \== T2,
    temporal_order(T3, T2, Index32),
    append([Index31, Index32], Index)
  ).

  
%---------------------------------------------------------------------------------------------------------
%
%  accessibility relation of possible worlds
%
%  to allow for as many deductions as possible the relation is reflexive, symmetric and transitive
%
%---------------------------------------------------------------------------------------------------------

% accessibility relation is reflexive
prolog_axiom_text(pw1, 'Prolog Axiom pw1: Accessibility relation is reflexive.').
prolog_axiom(accessibility_relation(World, World), _IndicesSoFar, [prolog_axiom(pw1)]).

% accessibility relation is symmetric
prolog_axiom_text(pw2, 'Prolog Axiom pw2: Accessibility relation is symmetric.').
prolog_axiom(accessibility_relation(World1, World2), _IndicesSoFar, [prolog_axiom(pw2)]) :-
  exists_asserted_atom(accessibility_relation(World2, World1), _Indices).

% accessibility relation is transitive
prolog_axiom_text(pw3, 'Prolog Axiom pw3: Accessibility relation is transitive.').
prolog_axiom(accessibility_relation(World1, World3), _IndicesSoFar, [prolog_axiom(pw3)]) :-
  exists_asserted_atom(accessibility_relation(World1, World2), _Indices12),
  exists_asserted_atom(accessibility_relation(World2, World3), _Indices23).


%---------------------------------------------------------------------------------------------------------
%
%  transitivity of comparative adjectives
%
%  example: John is older than Mary. Mary is older than Harry.|- John is older than Harry.
%  example: A dog is heavier than a cat. A cat is heavier than a mouse. |- A dog is heavier than a mouse.
%  example: Every dog is larger than a cat. Every cat is larger than a mouse. |- Every dog is larger than a mouse.
%  example. There is a dog. There is a cat. There is a mouse. Every dog is larger than every cat. Every cat is larger than every mouse. |- Every dog is larger than every mouse.
%           (proof needs only axioms 2, 4, 5)
%
%---------------------------------------------------------------------------------------------------------

prolog_axiom_text(transcompadj1, 'Prolog Axiom transcompadj1: Transitivity of comparative adjectives.').
prolog_axiom(predicate(World, _, be, _Object3, _Property), _IndicesSoFar, [prolog_axiom(transcompadj1)|Indices]) :-
  exists_asserted_atom(predicate(World, _, be, Object1, Property1), Indices1),
  exists_asserted_atom(property(World, Property1, _, comp_than, _), Indices1),
  exists_asserted_atom(predicate(World, _, be, Object2, Property2), Indices2),
  exists_asserted_atom(property(World, Property2, _, comp_than, _), Indices2),
  Object1 \== Object2,
  append(Indices1, Indices2, Indices).

prolog_axiom_text(transcompadj2, 'Prolog Axiom transcompadj2: Transitivity of comparative adjectives.').
prolog_axiom(predicate(World, _, be_NP, _Object3, _Property), _IndicesSoFar, [prolog_axiom(transcompadj2)|Indices]) :-
  exists_asserted_atom(predicate(World, _, be_NP, Object1, Property1), Indices1),
  exists_asserted_atom(property(World, Property1, _, comp_than, _), Indices1),
  exists_asserted_atom(predicate(World, _, be_NP, Object2, Property2), Indices2),
  exists_asserted_atom(property(World, Property2, _, comp_than, _), Indices2),
  Object1 \== Object2,
  append(Indices1, Indices2, Indices).


%---------------------------------------------------------------------------------------------------------
%
%  "do" as general expression of an activity
%
%  example: "John sleeps." -> "What does John do?"
%  example: "John is a man." -> "What does John do?"
%  example: "John sees a cat." -> "What does John do?"
%  example: "John and Mary see a cat." -> "What do John and Mary do?"
%  example: "John gives a cat a piece of some cheese." -> "What does John do?"
%  example: "John feeds a cat in the morning." -> "Who does what when?", "Who does do what when?"
%
%  concerning the treatment of the query word "what" see auxiliary axiom w9
%
%---------------------------------------------------------------------------------------------------------

% "do" can stand for the copula, intransitive, transitive and ditransitive verbs in queries
prolog_axiom_text(do, 'Prolog Axiom do: The verb "do" can stand for the copula, intransitive, transitive and ditransitive verbs.').
prolog_axiom(predicate(World, _VerbReferent, do, SubjectReferent, _QueryReferent), _IndicesSoFar, [prolog_axiom(do)|Indices]) :-
  (
    % intransitive verb
    exists_asserted_atom(predicate(World, _VerbReferentIV, Verb, SubjectReferent), Indices)
  ;
    % transitive verb
    exists_asserted_atom(predicate(World, _VerbReferentTV, Verb, SubjectReferent, _ObjectReferent), Indices)
  ;
    % ditransitive verb
    exists_asserted_atom(predicate(World, _VerbReferentDTV, Verb, SubjectReferent, _DirectObjectReferent, _IndirectObjectReferent), Indices)
  ),
  % store Verb to be used in auxiliary axiom w9
  (
   % remove modification of "be"
   (Verb == be_NP ; Verb == be_ID ; Verb == be_ADJ ; Verb == be_MOD)
   ->
   StoredVerb = be
  ;
   StoredVerb = Verb   
  ),
  assert(verb(StoredVerb)).
  

%---------------------------------------------------------------------------------------------------------
%
%  transform ditransitive verbs into their transtive form
%
%  positive example: 
%  "A manager gives a subordinate an order." -> "A manager gives an order."
%  example showing ACE's anophoric resolution that deviates from the standard interpretation: 
%  "A manager calls a subordinate. He gives him an order." -> "Who gives an order?" with who = subordinate
%
%---------------------------------------------------------------------------------------------------------
 
prolog_axiom_text(dtr_to_tr_verb, 'Prolog Axiom ditransitive_to_transitive_verb: Transform ditransitive verbs into their transtive form.').
prolog_axiom(predicate(World, _RefVerb, Verb, RefSubject, RefDirectObject), _IndicesSoFar, [prolog_axiom(dtr_to_tr_verb)|Indices]) :- 
  exists_asserted_atom(predicate(World, _, Verb, RefSubject, RefDirectObject, _RefIndirectObject), Indices), 
  exists_asserted_atom(object(World, RefDirectObject, _DirectObject, _, _, _, _), Indices).
  

%---------------------------------------------------------------------------------------------------------
%
%  presuppositions
%
%---------------------------------------------------------------------------------------------------------

% "A of B", respectively, "B's A" presuppose "B has A"
% example: John's cat sleeps. |- John has a cat.
% dubious example: John's health is bad. |– John has some health.
prolog_axiom_text(presupposition1, 'Prolog Axiom presupposition: "A of B", respectively, "B\'s A" presuppose "B has A"').
prolog_axiom(predicate(World, _Referent, have, Subject, Object), _IndicesSoFar, [prolog_axiom(presupposition1)|Indices]) :-
  exists_asserted_atom(relation(World, Object, _Noun, of, Subject), Indices).

% "B has A" presupposes "A of B", respectively, "B's A
% example: John has a cat that sleeps. |- John's cat sleeps.
prolog_axiom_text(presupposition2, 'Prolog Axiom presupposition: "B has A" presupposes "A of B", respectively, "B\'s A"').
prolog_axiom(relation(World, Object, _Noun, of, Subject), _IndicesSoFar, [prolog_axiom(presupposition2)|Indices]) :-
  exists_asserted_atom(predicate(World, _Referent, have, Subject, Object), Indices).


/* 
% 5 March 2025: terminated development since the approach chosen cannot be extended to handle negation
%---------------------------------------------------------------------------------------------------------
%
%  query "What is entailed?" generates all logical entailments of the axioms as simple positive declarative sentences
%  
%  current restriction: no negation
%
%  approach: 
%  – generate a DRS in standard format by composing a model of the axioms
%  – undo some transformations of drs_to_fol and fol_to_clauses
%  – translate the DRS into simple positive declarative ACE sentences
%
%---------------------------------------------------------------------------------------------------------

% two auxiliary axioms are needed to prove the "... is entailed" part of the query that cannot be derived from the axioms proper
prolog_axiom(property(_World, _Ref, entailed, pos), _IndicesSoFar, []).
prolog_axiom(predicate(_World, _Ref1, be_ADJ, _Ref2, _Ref3), _IndicesSoFar, []).

prolog_axiom_text(entailment, 'Entailed are all simple positive declarative sentences derivable from the axioms.').
prolog_axiom(query(_World, A, what), _IndicesSoFar, [prolog_axiom(entailment), what(Entailments)|Indices]) :-
  % get clauses
  user:clauses(Clauses),
  % there is a query asking for entailments
  member(satchmo_clause(Query, fail, [theorem(_)]), Clauses),
  subterm(entailed, Query), 
  % get model from elements stored in the Prolog data base
  findall(object(A, B, C, D, E, F, G),  user:object(A, B, C, D, E, F, G), Objects), 
  findall(property(A, B, C, D), user:property(A, B, C, D), Properties1),
  findall(property(A, B, C, D, E), user:property(A, B, C, D, E), Properties2),  
  findall(property(A, B, C, D, E, F, G), user:property(A, B, C, D, E, F, G), Properties3), 
  findall(relation(A, B, C, D, E), user:relation(A, B, C, D, E), Relations), 
  findall(predicate(A, B, C, D), user:predicate(A, B, C, D), Predicates1), 
  findall(predicate(A, B, C, D, E), user:predicate(A, B, C, D, E), Predicates2),  
  findall(predicate(A, B, C, D, E, F), user:predicate(A, B, C, D, E, F), Predicates3),  
  findall(modifier_adv(A, B, C, D), user:modifier_adv(A, B, C, D), Modifiers1), 
  findall(modifier_pp(A, B, C, D), user:modifier_pp(A, B, C, D), Modifiers2),  
  findall(has_part(A, B, C), user:has_part(A, B, C), HasParts), 
  findall(formula(A, B, C, D), user:formula(A, B, C, D), Formulas),
  append([Objects, Properties1, Properties2, Properties3, Relations, Predicates1, Predicates2, Predicates3, Modifiers1, Modifiers2, HasParts, Formulas], Model),
  % get indices and remove the World argument
  get_indices_and_remove_World_argument(Model, Clauses, Indices1, IntermediateModel1),
  % replace proper names  
  replace_proper_names(IntermediateModel1, IntermediateModel2), 
  % convert marked copula 'be_MOD', 'be_ADJ', 'be_ID' and 'be_NP' to 'be'
  convert_copula(IntermediateModel2, IntermediateModel3),
  % replace skolem terms by variables
  replace_skolem_terms_by_variables(IntermediateModel3, IntermediateModel4),
  % collect all variables
  term_variables(IntermediateModel4, Vars),
  % create DRS and translate it into ACE
  drs_to_ace(drs(Vars, IntermediateModel4), AllEntailments),
  % there can be duplicates
  sort(AllEntailments, [Entailments]).

get_indices_and_remove_World_argument(Model, Clauses, Indices, NewModel) :-
  get_indices_and_remove_World_argument(Model, Clauses, [], Indices, [], NewModel).
  
get_indices_and_remove_World_argument([], _Clauses, Indices, Indices, NewModel, NewModel).

get_indices_and_remove_World_argument([Element|Elements], Clauses, SofarIndices, Indices, SofarModel, NewModel) :- 
  % find in the Head of a clause a term matching Element to get the term's Index
  (  
    member(satchmo_clause(_Body, Head, [Index]), Clauses)
  ; 
    member(satchmo_clause(_Body, Head, [Index, _]), Clauses)
  ), 
  Head \= fail,
  % prevent variables to be instantiated
  \+ \+ subterm(Element, Head), 
  % remove World argument
  Element =.. [Functor, _World|Rest],
  NewElement =.. [Functor|Rest],
  % continue
  get_indices_and_remove_World_argument(Elements, Clauses, [Index|SofarIndices], Indices, [NewElement-Index|SofarModel], NewModel).


replace_proper_names(Model, NewModel) :-
  % eliminate all object definitions of proper names
  (
    % there is an object definition of a proper name
    member(object(Skolem, Name, named, na, eq, 1)-Index, Model)
    ->
    % delete it
    delete(Model, object(Skolem, Name, named, na, eq, 1)-Index, IntermediateModel1),
    % replace referent Skolem of the proper name Name in all other conditions by named(Name)
    substitute(Skolem, named(Name), IntermediateModel1, IntermediateModel2),
    % continue
    replace_proper_names(IntermediateModel2, NewModel)
  ;
    % there are no (more) object definitions of a proper names
    NewModel = Model
  ).
  

convert_copula(Model, NewModel) :-
  substitute(be_NP, be, Model, IntermediateModel1),
  substitute(be_MOD, be, IntermediateModel1, IntermediateModel2),
  substitute(be_ADJ, be, IntermediateModel2, IntermediateModel3),
  substitute(be_ID, be, IntermediateModel3, NewModel).


replace_skolem_terms_by_variables(Model, NewModel) :-
  (
    % find element that has skolem term Skolem as first argument
    member(Element-_Index, Model),
    Element =.. [_Functor, Skolem|_Rest],
    nonvar(Skolem), functor(Skolem, F, _), term_to_atom(F, A), atom_chars(A, [s, k |_])
    ->
    % replace Skolem by a new Variable
    substitute(Skolem, _Variable, Model, IntermediateModel),
    replace_skolem_terms_by_variables(IntermediateModel, NewModel)
  ;
    % no more elements to process
    NewModel = Model
  ).
*/

%---------------------------------------------------------------------------------------------------------
%
%  existence of somebody and something
%
%---------------------------------------------------------------------------------------------------------

% if there is a countable object different from something then there is somebody
% note: succeeds also for non-animate countable objects since animate and non-animate objects are not distinguished
prolog_axiom_text(s1, 'Prolog Axiom s1: If there is a countable object then there is somebody.').
prolog_axiom(object(World, Referent, somebody, countable, na, geq, 1), _IndicesSoFar, [prolog_axiom(s1), somebody(Op, Count, Noun, Properties)|Indices]) :-
  exists_asserted_atom(object(World, Referent, Noun, countable, _Unit, Op, Count), Indices),
  \+ Noun = something,
  findall(property(Degree, Adjective), exists_asserted_atom(property(World, Referent, Adjective, Degree), Indices), Properties).

% if there is an object then there is something
prolog_axiom_text(s2, 'Prolog Axiom s2: If there is an object then there is something.').
prolog_axiom(object(World, Referent, something, dom, na, na, na), _IndicesSoFar, [prolog_axiom(s2), something(Op, Count, Noun, Properties)|Indices]) :-
  exists_asserted_atom(object(World, Referent, Noun, Quant, _Unit, Op, Count), Indices),
  (Quant = countable ; Quant = mass), 
  % exclude 'something' trying to refer to 'something' which is proved directly
  \+ Noun = something,
  findall(property(Degree, Adjective), exists_asserted_atom(property(World, Referent, Adjective, Degree), Indices), Properties).

% if there is a proper name then there is somebody
prolog_axiom_text(s3, 'Prolog Axiom s3: If there is a proper name then there is somebody.').
prolog_axiom(object(World, Referent, somebody, countable, na, geq, 1), _IndicesSoFar, [prolog_axiom(s3), somebody(Name)|Indices]) :-
  exists_asserted_atom(object(World, Referent, Name, named, na, _Op, _Count), Indices).

% if there is a proper name then there is something
prolog_axiom_text(s4, 'Prolog Axiom s4: If there is a proper name then there is something.').
prolog_axiom(object(World, Referent, something, dom, na, na, na), _IndicesSoFar, [prolog_axiom(s4), something(Name)|Indices]) :-
  exists_asserted_atom(object(World, Referent, Name, named, na, _Op, _Count), Indices).


%---------------------------------------------------------------------------------------------------------
%
%  query words "who", "whose", "what" and "which"
%
%  current restriction: answer substitutions contain nouns and adjectives, not relative phrases
%
%---------------------------------------------------------------------------------------------------------

% if there are countable objects - including "somebody" - then the question "who" can be answered
prolog_axiom_text(w1, 'Prolog Axiom w1: If there are countable objects then the question "who" can be answered.').
prolog_axiom(query(World, A, who), _IndicesSoFar, [prolog_axiom(w1), who(Op1, C, B1, Properties)|Indices]) :-
  exists_asserted_atom(object(World, A, B, countable, na, Op, C), Indices),
  (
    % B is a conjunction of C nouns
    B = na
    ->
    Op1 = 'eq',
    B1 = 'conjunctive plural'
  ;
    % B is a single noun
    B1 = B,
    Op1 = Op
  ),
  % exclude the case that the query 'Who is XYZ?' results in the answer substitution 'who = ... XYZ'
  user:clauses(Clauses),
  member(satchmo_clause(Body, _Head, _), Clauses),
  support:subterm(query(World, A, who), Body), 
  \+ support:subterm(object(World, _, B, _, _, _, _), Body),
  findall(property(Degree, Adjective), exists_asserted_atom(property(World, A, Adjective, Degree), Indices), Properties).

% If there are named objects then the question "who" can be answered
prolog_axiom_text(w2, 'Prolog Axiom w2: If there are named objects then the question "who" can be answered.').
prolog_axiom(query(World, A, who), _IndicesSoFar, [prolog_axiom(w2), who(Name)|Indices]) :-
  exists_asserted_atom(object(World, A, Name, named, na, _Op, _Count), Indices),
  % exclude the case that the query 'Who is XYZ?' results in the answer substitution 'who = ... XYZ'
  user:clauses(Clauses),
  member(satchmo_clause(Body, _Head, _), Clauses),
  support:subterm(query(World, A, who), Body), 
  \+ support:subterm(object(World, _, Name, _, _, _, _), Body).

% if there are countable objects - including "somebody" - then the question "what" can be answered
prolog_axiom_text(w3, 'Prolog Axiom w3: If there are countable objects then the question "what" can be answered.').
prolog_axiom(query(World, A, what), IndicesSoFar, [prolog_axiom(w3), what(Op1, C, B1, Properties)|Indices]) :-
  % do not use together with auxiliary axioms involving "do"
  \+ member(prolog_axiom(do), IndicesSoFar),
  \+ member(prolog_axiom(donegiv), IndicesSoFar), 
  \+ member(prolog_axiom(donegtv), IndicesSoFar), 
  \+ member(prolog_axiom(donegdv), IndicesSoFar), 
  exists_asserted_atom(object(World, A, B, countable, na, Op, C), Indices),
  (
    % B is a conjunction of C nouns
    B = na
    ->
    Op1 = 'eq',
    B1 = 'conjunctive plural'
  ;
    % B is a single noun
    B1 = B,
    Op1 = Op
  ),
  % exists_asserted_atom(predicate(World, _, be_NP, A, _), Indices), % deactivated 14022018: unclear condition
  % exclude case '... Noun of ...'                                   
  %  \+ exists_asserted_atom(relation(World, A, _Noun, of, _), _),   % deactivated 14022018: perhaps superfluous
  % exclude the case that the query 'What is XYZ?' results in the answer substitution 'what = ... XYZ'
  user:clauses(Clauses),
  member(satchmo_clause(Body, _Head, _), Clauses),
  support:subterm(query(World, A, what), Body), 
  \+ support:subterm(object(World, _, B1, _, _, _, _), Body),
  findall(property(Degree, Adjective), exists_asserted_atom(property(World, A, Adjective, Degree), Indices), Properties).

% If there are named objects then the question "what" can be answered
prolog_axiom_text(w4, 'Prolog Axiom w4: If there are named objects then the question "what" can be answered.').
prolog_axiom(query(World, A, what), IndicesSoFar, [prolog_axiom(w4), what(Name)|Indices]) :-
  % do not use together with auxiliary axioms involving "do"
  \+ member(prolog_axiom(do), IndicesSoFar),
  \+ member(prolog_axiom(donegiv), IndicesSoFar), 
  \+ member(prolog_axiom(donegtv), IndicesSoFar), 
  \+ member(prolog_axiom(donegdv), IndicesSoFar), 
  exists_asserted_atom(object(World, A, Name, named, na, _Op, _Count), Indices),
  % exclude the case that the query 'What is XYZ?' results in the answer substitution 'what = ... XYZ'
  user:clauses(Clauses),
  member(satchmo_clause(Body, _Head, _), Clauses),
  support:subterm(query(World, A, what), Body), 
  \+ support:subterm(object(World, _, Name, _, _, _, _), Body).

% if there is a mass object then the question "what" can be answered
prolog_axiom_text(w5, 'Prolog Axiom w5: If there is a mass object then the question "what" can be answered.').
prolog_axiom(query(World, A, what), IndicesSoFar, [prolog_axiom(w5), what(B, Properties)|Indices]) :-
  % do not use together with auxiliary axioms involving "do"
  \+ member(prolog_axiom(do), IndicesSoFar),
  \+ member(prolog_axiom(donegiv), IndicesSoFar), 
  \+ member(prolog_axiom(donegtv), IndicesSoFar), 
  \+ member(prolog_axiom(donegdv), IndicesSoFar), 
  exists_asserted_atom(object(World, A, B, mass, na, na, na), Indices),
  % exclude the case that the query 'What is XYZ?' results in the answer substitution 'what = ... XYZ'
  user:clauses(Clauses),
  member(satchmo_clause(Body, _Head, _), Clauses),
  support:subterm(query(World, A, what), Body), 
  \+ support:subterm(object(World, _, B, _, _, _, _), Body),
  findall(property(Degree, Adjective), exists_asserted_atom(property(World, A, Adjective, Degree), Indices), Properties).
  
% if there is something then the question "what" can be answered
prolog_axiom_text(w6, 'Prolog Axiom w6: If there is something then the question "what" can be answered.').
prolog_axiom(query(World, A, what), IndicesSoFar, [prolog_axiom(w6), what(something)|Indices]) :-
  % do not use together with auxiliary axioms involving "do"
  \+ member(prolog_axiom(do), IndicesSoFar),
  \+ member(prolog_axiom(donegiv), IndicesSoFar), 
  \+ member(prolog_axiom(donegtv), IndicesSoFar), 
  \+ member(prolog_axiom(donegdv), IndicesSoFar), 
  exists_asserted_atom(object(World, A, something, dom, na, na, na), Indices).

% if there is a list then the question "what" can be answered
% example: There is a list L of ["append", [1,2,3], [4,5,6], L].|- What is a list?
prolog_axiom_text(w7, 'Prolog Axiom w7: If there is a list then the question "what" can be answered.').
prolog_axiom(query(World, A, what), IndicesSoFar, [prolog_axiom(w7), what(List)|Indices]) :-
  % do not use together with auxiliary axioms involving "do"
  \+ member(prolog_axiom(do), IndicesSoFar),
  \+ member(prolog_axiom(donegiv), IndicesSoFar), 
  \+ member(prolog_axiom(donegtv), IndicesSoFar), 
  \+ member(prolog_axiom(donegdv), IndicesSoFar), 
  exists_asserted_atom(object(World, A, list, countable, na, geq, 1), Indices),
  b_getval(A, (List,Indices)).
% companion to w7 to prove the predicate/5 part of the question "what is ..."
prolog_axiom(predicate(World, _ReferentPredicate, be_NP, _What, NounReferent), IndicesSoFar, []) :-
  memberchk(prolog_axiom(w7), IndicesSoFar),
  exists_asserted_atom(object(World, NounReferent, list, countable, na, geq, 1), _Indices),
  % prevent unintended backtracking
  !.

/*
% if there is a number or an expression then the question "what is ..." can be answered
% example: answer_question('The root of 2 is 2^(1/2).', 'What is the root of 2?', [], M, T, P, W).
prolog_axiom_text(w7, 'Prolog Axiom w7: If there is a number or an expression then the question "what" can be answered.').
prolog_axiom(query(World, _Referent, what), _IndicesSoFar, [prolog_axiom(w7), what(NounResult)|Indices]) :-
  exists_asserted_atom(formula(World, NounReferent, =, RHS), Indices1),
  (RHS = int(_) ; RHS = real(_) ; RHS = expr(_,_,_)),
  exists_asserted_atom(object(World, NounReferent, Noun, _, _, _, _), Indices2),
  \+ Noun = something,
  % prevent unintended backtracking
  !,
  b_getval(NounReferent, (Value, Indices3)),
  % identify integers
  (
    number(Value)
    ->
    IntegerValue is floor(Value), (Value =:= IntegerValue -> Result = IntegerValue; Result = Value)
  ;
    % case: answer_query('There is a number C of some cows.', 'What is a number of some cows?', [], M, T, P, W).
    % does not instantiate Value
    fail
  ),
  (
    % case: "... a Noun of GenitiveNoun is RHS ...
    exists_asserted_atom(object(World, GenitiveReferent, GenitiveNoun, _, _, _, _), Indices2),
    exists_asserted_atom(relation(World, NounReferent, Noun, of, GenitiveReferent), Indices2)
    ->
    atomic_list_concat([Noun, ' of ', GenitiveNoun, ' is ', Result], NounResult)
  ;
    % case: "... a Noun is RHS ...
    atomic_list_concat([Noun, ' is ', Result], NounResult)
  ),
  append([Indices1, Indices2, Indices3], AllIndices),
  flatten(AllIndices, FlattenedAllIndices), 
  sort(FlattenedAllIndices, Indices).
% companion to w7 to prove the predicate/5 part of the question "what is ..."
prolog_axiom(predicate(World, _ReferentPredicate, be_NP, _What, NounReferent), _IndicesSoFar, []) :-
  exists_asserted_atom(formula(World, NounReferent, =, RHS), _Indices1),
  (RHS = int(_) ; RHS = real(_) ; RHS = expr(_,_,_)),
  exists_asserted_atom(object(World, NounReferent, Noun, _, _, _, _), _Indices2),
  \+ Noun = something.
*/

% if there are numbers, expressions or linear equations then the question "what" can be answered
prolog_axiom_text(w8, 'Prolog Axiom w8: If there are numbers, expressions or linear equations then the question "what" can be answered.').
prolog_axiom(query(World, Referent, what), IndicesSoFar, [prolog_axiom(w8), what(NounResult)|Indices]) :-
  % do not use together with auxiliary axioms involving "do"
  \+ member(prolog_axiom(do), IndicesSoFar),
  \+ member(prolog_axiom(donegiv), IndicesSoFar), 
  \+ member(prolog_axiom(donegtv), IndicesSoFar), 
  \+ member(prolog_axiom(donegdv), IndicesSoFar), 
  user:clauses(Clauses),
  member(satchmo_clause(Body, _Head, _QueryIndex), Clauses),
  support:subterm(query(World, Referent, what), Body),
  support:subterm(object(World, NounReferent, Noun, _, _, _, _), Body), 
  exists_asserted_atom(object(World, NounReferent, Noun, _, _, _, _), Index),
  b_getval(NounReferent, (Value, SkolemIndex)),
%%%%%% inserted instead of the following inactivated code
  append(Index, SkolemIndex, RawIndices),
  flatten(RawIndices, FlattenedRawIndices), 
  sort(FlattenedRawIndices, Indices),
%%%%%%
/* 
% 13 Aug 2021: inactivated because prevents output of all axioms needed for an arithmetic proof
% reason for this code?
  (
    SkolemIndex = [SkolemIndexValue],
    nonvar(SkolemIndexValue)
    ->
    append(Index, SkolemIndex, RawIndices),
    flatten(RawIndices, FlattenedRawIndices), 
    sort(FlattenedRawIndices, Indices)
  ;
    Indices = Index
  ),
*/
  (
    number(Value)
    ->
    IntegerValue is floor(Value), (Value =:= IntegerValue -> Result = IntegerValue; Result = Value)
  ;
    % case: answer_query('There is a number C of some cows.', 'What is a number of some cows?', [], M, T, P, W).
    % does not instantiate Value
    fail
  ),
  (
    % case: ... Noun of GenitiveNoun is ... where GenitiveNoun is a common noun
    % example: A number of some cows is 2. |- What is a number of some cows?
    % example: The capital C is 1000.00. The interest I is 0.0025. The yearly fee F is 12.00. The duration D is 10. The balance of the account is C *(1+I)^D - F*(1+I)^(D - 1) - F. |- What is the balance of the account?
    % example: There is a number C of some cows. There is a number D of some ducks. C+D=100. 4*C+2*D=260. |- What is a number of some cows?
    % example: There is a number C of some cows. There is a number D of some ducks. C+D=100. 4*C+2*D=260. |- What is a number of some cows? What is a number of some ducks?
    support:subterm(relation(World, NounReferent, Noun, of, GenitiveNounReferent), Body),
    exists_asserted_atom(relation(World, NounReferent, Noun, of, GenitiveNounReferent), Index),
    (
      support:subterm(object(World, GenitiveNounReferent, GenitiveNoun, _, _, _, _), Body), 
      exists_asserted_atom(object(World, GenitiveNounReferent, GenitiveNoun, _, _, _, _), Index)
      ->
      Genitive = GenitiveNoun
    ;
      % case: ... Noun of GenitiveNoun is ... where GenitiveNoun is a number
      % example: The root of 2 is 2^(1/2). |- What is the root of 2?
      (GenitiveNounReferent = int(Number) ; GenitiveNounReferent = real(Number))
      ->
      Genitive = Number
    )
    ->
    atomic_list_concat([Noun, ' of ', Genitive, ' is ', Result], NounResult)
  ;
    % case: ... Noun is ...
    % example: A number is 2/3. |- What is a number?
    \+ support:subterm(relation(World, NounReferent, Noun, of, _GenitiveNounReferent), Body),
    atomic_list_concat([Noun, ' is ', Result], NounResult)
  ).

% companion to w8 to prove the predicate/5 part of the question "what is ..."
prolog_axiom(predicate(World, _ReferentPredicate, be_NP, _What, NounReferent), IndicesSoFar, []) :-
  memberchk(prolog_axiom(w8), IndicesSoFar),
  exists_asserted_atom(object(World, NounReferent, Noun, _, _, _, _), _Indices),
  \+ Noun = something, 
  % prevent unintended backtracking
  !. 

% "what" occurs in queries like "What does/do ... do?"
% prolog_axiom(do) processes the "do" part
prolog_axiom_text(w9, 'Prolog Axiom w9: The query word "what" is part of the query "What does/do ... do?" and stands for a verb.').
prolog_axiom(query(World, _Referent, what), _IndicesSoFar, [prolog_axiom(w9), what(Verb)]) :-
  % query is "What does/do ... do?
  user:clauses(Clauses),
  member(satchmo_clause(Body, Head, _QueryIndex), Clauses),
  (
    % case: positive "do"
    support:subterm(query(World, QueryReferent, what), Body),
    support:subterm(predicate(World, _VerbReferent, do, _NounReferent, QueryReferent), Body)
  ;
    % case: negated "do"
    support:subterm(query(World, QueryReferent, what), Head),
    support:subterm(predicate(World, _VerbReferent, do, _NounReferent, QueryReferent), Head)
  ),
  % get verb stored in auxiliary axiom "do"
  retract(verb(Verb)).

/*
% if there are linear equations then the question "what" can be answered
% example: answer_query('There is a number C of some cats. There is a number D of some dogs. C+D=3. C-D=1.', 
% 'What is the number of some dogs? What is the number of some cats?', [], M, T, P, W).
prolog_axiom_text(w8, 'Prolog Axiom w8: If there are linear equations then the question "what" can be answered.').
prolog_axiom(query(World, Referent, what), _IndicesSoFar, [prolog_axiom(w8), what(NounResult)|Indices]) :-
  findall((Noun, Value, FinalIndex),
           (
             exists_asserted_atom(object(World, Skolem, NounReferent, _, _, _, _), Index),
             exists_asserted_atom(relation(World,Skolem, NounReferent, of, GenitiveReferent), Index),
             exists_asserted_atom(object(World, GenitiveReferent, Noun, _, _, _, _), Index),
             b_getval(Skolem, (Value, SkolemIndex)),
             append(Index, SkolemIndex, RawIndex),
             flatten(RawIndex, FlattenedRawIndex), 
             sort(FlattenedRawIndex, FinalIndex)
           ),
         NounsValuesIndices
         ),
  collect_results_and_indices(NounsValuesIndices, NounsValues, Indices),
  user:clauses(Clauses),
  member(satchmo_clause(Body, _Head, _Index), Clauses),
  support:subterm(query(World, Referent, what), Body),
  support:subterm(relation(World, _Skolem, Noun, of, GenitiveNoun), Body),
  support:subterm(object(World, _Skolem, GenitiveNoun, _, _, _, _), Body), 
  member((GenitiveNoun-Value), NounsValues),
  (
    number(Value)
    ->
    IntegerValue is floor(Value), (Value =:= IntegerValue -> Result = IntegerValue; Result = Value),
    atomic_list_concat([Noun, ' of ', GenitiveNoun, ' is ', Result], NounResult)
  ;
    % case: answer_query('There is a number C of some cows.', 'What is a number of some cows?', [], M, T, P, W).
    % does not instantiate Value
    fail
  ).

collect_results_and_indices(NounsValuesIndices, NounsValues, IndividualIndices) :-
  collect_results_and_indices(NounsValuesIndices, [], NounsValues, [], IndividualIndices).

collect_results_and_indices([], NounsValues, NounsValues, IndividualIndices, IndividualIndices).
  
collect_results_and_indices([(Noun, Value, Index) | NounsValuesIndices], NounsValuesSoFar, NounsValues, IndicesSoFar, Indices) :-
  collect_results_and_indices(NounsValuesIndices, [Noun-Value|NounsValuesSoFar], NounsValues, [Index|IndicesSoFar], Indices).
*/

/*
% if there is a number then the question "what" can be answered
prolog_axiom_text(w7, 'Prolog Axiom w7: If there is a number then the question "what" can be answered.').
prolog_axiom(query(World, A, what), _IndicesSoFar, [prolog_axiom(w7), what(Number)|Indices]) :-
  exists_asserted_atom(object(World, ReferentNoun, _Noun, _, _, _, _), _Indices),
  (
    exists_asserted_atom(predicate(World, _ReferentPredicate, be_NP, ReferentNoun, A), Indices),
    (A = int(Number) ; A = real(Number))
    ->
    true
  ;
    exists_asserted_atom(predicate(World, _ReferentPredicate, be_NP, A, ReferentNoun), Indices),
    (A = int(Number) ; A = real(Number))
    ->
    true
  ).

% if there is an expression then the question "what" can be answered
prolog_axiom_text(w8, 'Prolog Axiom w8: If there is an expression then the question "what" can be answered.').
prolog_axiom(query(World, A, what), _IndicesSoFar, [prolog_axiom(w8), what(Value)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _ReferentPredicate, be_NP, ReferentNoun, A), IndexOfExpression)
  ;
    exists_asserted_atom(predicate(World, _ReferentPredicate, be_NP, A, ReferentNoun), IndexOfExpression)
  ),
  A = expr(_Operator, _Argument1, _Argument2),
  exists_asserted_atom(object(World, ReferentNoun, _Noun, _, _, _, _), IndexOfExpression),
  evaluate_expression(A, IndexOfExpression, Value, IndicesOfValues),
  append(IndexOfExpression, IndicesOfValues, Indices).

evaluate_expression(expr(Operator, Argument1, Argument2), IndexOfOriginalExpression, Value, Indices) :-
  convert_argument_to_value(Argument1, IndexOfOriginalExpression, Value1, Indices1), 
  convert_argument_to_value(Argument2, IndexOfOriginalExpression, Value2, Indices2), 
  append(Indices1, Indices2, Indices),
  % use Prolog's "is"-operator to evaluate the expression
  Expression =.. [Operator, Value1, Value2],
  Value is Expression.
 
convert_argument_to_value(Argument, IndexOfOriginalExpression, Value, Indices) :-
  (
    % argument is an integer
    Argument = int(Value)
    -> 
    Indices = []
  ;
    % argument is a real
    Argument = real(Value)
    -> 
    Indices = []
  ;
    % argument is an expression
    Argument = expr(Operator, Argument1, Argument2)
    -> 
    evaluate_expression(expr(Operator, Argument1, Argument2), IndexOfOriginalExpression, Value, Indices)
  ;
    % argument is skolem term pointing to a value defined elsewhere
    functor(Argument, Name, _Arity), \+ Name = [], sub_atom(Name, 0, _, _, sk),
    -> 
    (
      % value of skolem term is found
      (
        exists_asserted_atom(predicate(_World, _PredicateReferent, be_NP, Argument, RawValue), Indices)
      ;
        exists_asserted_atom(predicate(_World, _PredicateReferent, be_NP, RawValue, Argument), Indices)
      )
      ->
      convert_argument_to_value(RawValue, IndexOfOriginalExpression, Value, _Indices)
    ;
      % value of skolem term cannot be found, i.e. expression contains uninstantiated variables
      % set Value to 0 to be able to continue without arithmetic errors generated by SWI Prolog
      Value = 0,
      Indices = [], 
      % create error message
      % note: since the ACE form of the expression is not available the expression is not shown in the error message
      IndexOfOriginalExpression = [SourceIndex],
      SourceIndex =.. [Source, Index],
      atomic_list_concat(['An expression in ', Source, ' ', Index, ' cannot be evaluated since some of its terms do not evaluate to numbers.'], MessageText),
      add_error_message(race, Index-'', MessageText, 'Check input.')
    )
  ).
*/

/*
% if there are linear equations then the question "what" can be answered
prolog_axiom_text(w9, 'Prolog Axiom w9: If there are linear equations then the question "what" can be answered.').
prolog_axiom(query(World, A, what), _IndicesSoFar, [prolog_axiom(w9), what(NounValue)|Indices]) :-
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
  member(satchmo_clause(Body, _Head, _Index), Clauses),
  support:subterm(query(World, A, what), Body),
  support:subterm(relation(World, _Skolem, LinkNoun, of, Noun), Body),
  support:subterm(object(World, _Skolem, Noun, _, _, _, _), Body),
  member((Noun-Value), NounsValues),
  NounValue=[Noun-Value],
  append(IndividualIndices, IndicesOfFormulas, RawIndices),
  flatten(RawIndices, FlattenedIndices),
  list_to_set(FlattenedIndices, Indices).

collect_results_and_indices(NounsValuesIndices, NounsValues, IndividualIndices) :-
  collect_results_and_indices(NounsValuesIndices, [], NounsValues, [], IndividualIndices).

collect_results_and_indices([], NounsValues, NounsValues, IndividualIndices, IndividualIndices).
  
collect_results_and_indices([(Noun, Value, Index) | NounsValuesIndices], NounsValuesSoFar, NounsValues, IndicesSoFar, Indices) :-
  collect_results_and_indices(NounsValuesIndices, [Noun-Value|NounsValuesSoFar], NounsValues, [Index|IndicesSoFar], Indices).


substitute_skolem_terms_by_variables(Formulas, NewFormulas, Substitutions) :-
  substitute_skolem_terms_by_variables(Formulas, NewFormulas, [], Substitutions).

substitute_skolem_terms_by_variables(Formulas, NewFormulas, SubstitutionsSoFar, Substitutions) :-
  (
    support:subterm(Skolem, Formulas),
    functor(Skolem, Name, _Arity), 
    \+ Name = [],
    sub_atom(Name, 0, _, _, sk)
    ->
    substitute(Skolem, Variable, Formulas, IntermediateFormulas),
    substitute_skolem_terms_by_variables(IntermediateFormulas, NewFormulas, [Skolem-Variable|SubstitutionsSoFar], Substitutions)
  ;
    NewFormulas = Formulas,
    Substitutions = SubstitutionsSoFar
  ).
*/

/*
convert_formulas([], []).

convert_formulas([{formula(LHS, = ,RHS)} | RestFormulas], [{ConvertedLHS = ConvertedRHS} | ConvertedRestFormulas])  :-
  convert(LHS, ConvertedLHS),
  convert(RHS, ConvertedRHS),
  convert_formulas(RestFormulas, ConvertedRestFormulas).
  
convert(X,X) :-
  var(X).

convert(+, +) :- 
  !.

convert(-, -) :- 
  !.

convert(*, *) :- 
  !.

convert(/, /) :- 
  !.

convert(^, ^) :- 
  !.

convert(int(X), X) :- 
  !.

convert(real(X), X) :- 
  !.

convert(expr(Operator, LHS, RHS), ConvertedExpression) :-
  (Operator = + ; Operator = - ; Operator = * ; Operator = / ; Operator = ^)
  ->
  convert(LHS, ConvertedLHS),
  convert(RHS, ConvertedRHS),
  ConvertedExpression =.. [Operator, ConvertedLHS, ConvertedRHS],
  !.
  
  
execute_formulas([]).

execute_formulas([Formula|Formulas]) :-
  call(Formula),
  execute_formulas(Formulas).
*/

% if there are countable objects - including "somebody" - then the question "whose" can be answered
prolog_axiom_text(w10, 'Prolog Axiom w10: If there are countable objects then the question "whose" can be answered.').
prolog_axiom(query(World, A, whose), _IndicesSoFar, [prolog_axiom(w10), whose(Op, C, B, Properties)|Indices]) :-
  exists_asserted_atom(object(World, A, B, countable, na, Op, C), Indices),
  findall(property(Degree, Adjective), exists_asserted_atom(property(World, A, Adjective, Degree), Indices), Properties).

% If there are named objects then the question "whose" can be answered
prolog_axiom_text(w11, 'Prolog Axiom w11: If there are named objects then the question "whose" can be answered.').
prolog_axiom(query(World, A, whose), _IndicesSoFar, [prolog_axiom(w11), whose(Name)|Indices]) :-
  exists_asserted_atom(object(World, A, Name, named, na, _Op, _Count), Indices).

% if there is a mass object then the question "whose" can be answered
prolog_axiom_text(w12, 'Prolog Axiom w12: If there is a mass object then the question "whose" can be answered.').
prolog_axiom(query(World, A, whose), _IndicesSoFar, [prolog_axiom(w12), whose(B, Properties)|Indices]) :-
  exists_asserted_atom(object(World, A, B, mass, na, na, na), Indices),
  findall(property(Degree, Adjective), exists_asserted_atom(property(World, A, Adjective, Degree), Indices), Properties).
  
% if there is something then the question "whose" can be answered
prolog_axiom_text(w13, 'Prolog Axiom w13: If there is something then the question "whose" can be answered.').
prolog_axiom(query(World, A, whose), _IndicesSoFar, [prolog_axiom(w13), whose(something)|Indices]) :-
  exists_asserted_atom(object(World, A, something, dom, na, na, na), Indices).

% if there are countable objects then the question "which" can be answered
% example: 'Beaky is a bird that flies.', 'Which bird flies?', which = (at least 1) bird
prolog_axiom_text(w14, 'Prolog Axiom w14: If there are countable objects then the question "which" can be answered.').
prolog_axiom(query(World, A, which(Noun)), _IndicesSoFar, [prolog_axiom(w14), which(Op, C, Noun, Properties)|Indices]) :-
  % exclude the case that the query 'Which ... is XYZ?' results in the answer substitution 'which = XYZ' by
  % a restriction in the Prolog axiom reflexivity_NP
  exists_asserted_atom(object(World, A, Noun, countable, na, Op, C), Indices),
  findall(property(Degree, Adjective), exists_asserted_atom(property(World, A, Adjective, Degree), Indices), Properties).

% if there are mass objects then the question "which" can be answered
prolog_axiom_text(w15, 'Prolog Axiom w15: If there is a mass object then the question "which" can be answered.').
prolog_axiom(query(World, A, which(Noun)), _IndicesSoFar, [prolog_axiom(w15), which(Noun, Properties)|Indices]) :-
  % exclude the case that the query 'Which ... is XYZ?' results in the answer substitution 'which = XYZ' by
  % a restriction in the Prolog axiom reflexivity_NP
  exists_asserted_atom(object(World, A, Noun, mass, na, na, na), Indices),
  findall(property(Degree, Adjective), exists_asserted_atom(property(World, A, Adjective, Degree), Indices), Properties).

% if there are named objects then the question "which" can be answered
% example: 'Spanish is an official language of Spain.'|- 'Which language is an official language of Spain?',  which = Spanish
% example: 'Beaky is a bird that flies.', 'Which bird flies?', which = Beaky 
prolog_axiom_text(w16, 'Prolog Axiom w16: If there are named objects then the question "which" can be answered.').
prolog_axiom(query(World, A, which(Noun)), _IndicesSoFar, [prolog_axiom(w16), which(Name)|Indices]) :-
  exists_asserted_atom(predicate(World, _, be_NP, B, A), Indices1),  
  exists_asserted_atom(object(World, A, Noun, countable, na, geq, 1), Indices2),
  exists_asserted_atom(object(World, B, Name, named, na, eq, 1), Indices3),
  append([Indices1, Indices2, Indices3], Indices).


%---------------------------------------------------------------------------------------------------------
%
%  query words "how", "when" and "where"
%
%  current restriction: answer substitutions for PP's contain nouns and adjectives, not relative phrases
%
%---------------------------------------------------------------------------------------------------------

% if there is a verb modified by an adverb or a prepositional phrase then the questions "how", "where" and "when" can be answered
% since "where" and "when" are interpreted as "how" a warning message is created
prolog_axiom_text(w21, 'Prolog Axiom w21: If there is a verb modified by an adverb or a prepositional phrase then the questions "how", "where" and "when" can be answered.').
prolog_axiom(query(World, Referent, QueryWord), _IndicesSoFar, [prolog_axiom(w21), Modifier|Indices]) :-
  (QueryWord = how ; QueryWord = where ; QueryWord = when),
  (
    exists_asserted_atom(predicate(World, Referent, _Verb, _Subject), Indices1)
  ;
    exists_asserted_atom(predicate(World, Referent, _Verb, _Subject, _Object), Indices1)
  ;
    exists_asserted_atom(predicate(World, Referent, _Verb, _Subject, _DirectObject, _IndirectObject), Indices1)
  ),
  (
    exists_asserted_atom(modifier_adv(World, Referent, Adverb, Degree), Indices1),
    Modifier = how(Degree, Adverb),
    Indices = Indices1
  ;
    exists_asserted_atom(modifier_pp(World, Referent, Preposition, NounReferent), Indices1),
    find_noun_phrase_for_preposition(NounReferent, Noun, Domain, Op, C, Properties, Indices2),
    (Domain = countable -> Modifier = how(Preposition, Op, C, Noun, Properties) ; Modifier = how(Preposition, Noun, Properties)),
    append(Indices1, Indices2, Indices)
  ),
  (
    QueryWord \= how
    ->
    atomic_list_concat(['The query word "', QueryWord, '" was interpreted as the query word "how".'], MessageText),
    add_warning_message_once('query answering', '', MessageText, '')
  ;
    true
  ).

% if there is a copula plus an adjective plus a prepositional phrase, as for example in "Paris is located in France."
% then the questions "how", "where" and "when" can be answered
% since "where" and "when" are interpreted as "how" a warning message is created
prolog_axiom_text(w22, 'Prolog Axiom w22: If there is a copula plus an adjective plus a prepositional phrase then the questions "how", "where" and "when" can be answered.').
prolog_axiom(query(World, _Referent, QueryWord), _IndicesSoFar, [prolog_axiom(w22), Modifier|Indices]) :-
  (QueryWord = how ; QueryWord = where ; QueryWord = when),
  exists_asserted_atom(predicate(World, VerbReferent, be_ADJ, _Subject, AdjectiveReferent), Indices1),
  exists_asserted_atom(property(World, AdjectiveReferent, _Adjective, _Degree), Indices1),
  exists_asserted_atom(modifier_pp(World, VerbReferent, Preposition, NounReferent), Indices1),
  find_noun_phrase_for_preposition(NounReferent, Noun, Domain, Op, C, Properties, Indices2),
  (Domain = countable -> Modifier = how(Preposition, Op, C, Noun, Properties) ; Modifier = how(Preposition, Noun, Properties)),
  append(Indices1, Indices2, Indices),
  (
    QueryWord \= how
    ->
    atomic_list_concat(['The query word "', QueryWord, '" was interpreted as the query word "how".'], MessageText),
    add_warning_message_once('query answering', '', MessageText, '')
  ;
    true
  ).

find_noun_phrase_for_preposition(NounReferent, Noun, Domain, Op, C, Properties, Indices) :-
  exists_asserted_atom(object(World, NounReferent, Noun, Domain, _, Op, C), Indices),
  findall(property(Degree, Adjective), exists_asserted_atom(property(World, NounReferent, Adjective, Degree), Indices), Properties).

find_noun_phrase_for_preposition(NounReferent, Noun, Domain, Op, C, Properties, Indices) :-
  (
    exists_asserted_atom(predicate(_World, _Referent, be_NP, NounReferent, NewNounReferent), _NewIndices)
    ->
    find_noun_phrase_for_preposition(NewNounReferent, Noun, Domain, Op, C, Properties, Indices)
  ;
    fail
  ).


%---------------------------------------------------------------------------------------------------------
%
%  query words "how many" and "how much"
%
%
%---------------------------------------------------------------------------------------------------------

% if there are countable objects then the question "how many" can be answered
% axiom works only for integers including 0 and "at least"
% axiom does not work for "no", "does/is not", "more than", "less than", "at most"
prolog_axiom_text(w31, 'Prolog Axiom w31: If there are countable objects then the question "how many" can be answered.').
prolog_axiom(query(World, Referent, how_many(Body)), _IndicesSoFar, [prolog_axiom(w31), Result|Indices]) :- 
  % find all solutions for Noun
  support:subterm(object(World, Referent, Noun, countable, na, geq, _Count), Body), 
  findall((Count, Index), 
                          (
                            % individual solutions
                            exists_asserted_atom(object(World, Referent, Noun, countable, na, geq, Count), _),
                            % prove Body
                            satchmo:prove_body(Body, [], [], Index)
                          ;
                            % aggregate solutions
                            (
                              % there are aggregate solutions 
                              aggregation(Referent, Body, Count, Index)
                              ->
                              true
                            ;
                              % there are no aggregate solutions
                              % mark this situation by Count = 0, Indices = []
                              Count = 0,
                              Indices = []
                            )
                          ), 
                          CountsIndices),
  (
    CountsIndices \= [], 
    CountsIndices \= [(0, _)]
    ->
    % determine the solution with the maximal cardinality
    % set Measure argument to na
    find_maximal_count(CountsIndices, how_many, na, Result, Indices)
  ;
    % there are no solutions
    fail
  ).

% if there are mass objects then the question "how much" can be answered
prolog_axiom_text(w32, 'Prolog Axiom w32: If there are mass objects then the question "how much" can be answered.').
prolog_axiom(query(World, Referent, how_much(Body)), _IndicesSoFar, [prolog_axiom(w32), how_much(some, [])|Indices]) :-
  % find a solution for Noun
  exists_asserted_atom(object(World, Referent, _Noun, mass, na, na, na), _),
  % prove Body
  satchmo:prove_body(Body, [], [], Indices).
  /* deactivated 22 August 2012 since reporting only adjectives does not make much sense if nothing else – for instance relative clauses – is reported 
  % find adjectives of Noun that are not occurring in query
  findall(property(Degree, Adjective), (exists_asserted_atom(property(World, Referent, Adjective, Degree), Indices), \+ support:subterm(property(World, _Referent, Adjective, Degree), RestBody)), Properties).
  */

% if there are measurement nouns then the question "how much" can be answered
prolog_axiom_text(w33, 'Prolog Axiom w33: If there are measurement nouns then the question "how much" can be answered.').
prolog_axiom(query(World, Referent, how_much(Body)), _IndicesSoFar, [prolog_axiom(w33), Result|Indices]) :- 
  % fix Measure so that different measurement units, e.g. l or kg, are treated separately
  support:subterm(object(World, Referent, Noun, mass, _Measure, geq, _Count), Body),
  exists_asserted_atom(object(World, _, Noun, mass, Measure, _, _), _),
  % find all solutions for Noun
  findall((Count, Index), 
                          (
                            % individual solutions
                            exists_asserted_atom(object(World, Referent, Noun, mass, Measure, geq, Count), _),
                            % prove Body
                            satchmo:prove_body(Body, [], [], Index)
                          ;
                            % aggregate solutions
                            (
                              % there are aggregate solutions 
                              aggregation(Referent, Body, Count, Index)
                              ->
                              true
                            ;
                              % there are no aggregate solutions
                              % mark this situation by Count = 0, Indices = []
                              Count = 0,
                              Indices = []
                            )
                          ), 
                          CountsIndices),
  (
    CountsIndices \= [], 
    CountsIndices \= [(0, _)]
    ->
    % determine the solution with the maximal cardinality
    find_maximal_count(CountsIndices, how_much, Measure, Result, Indices)
  ;
    fail
  ).


find_maximal_count(CountsIndices, QueryWord, Measure, Result, Indices) :-
  (
    % there are no aggregate solutions 
    select((0, []), CountsIndices, RemainingCountsIndices)
    -> 
    find_maximal_count1(RemainingCountsIndices, 0, MaxCount, [], _MaxIndices), 
    get_all_counts_and_indices(RemainingCountsIndices, AllCounts, AllIndices),
    (
      AllCounts \= [_]
      ->
      Result =.. [QueryWord, geq, MaxCount, Measure, [text('calculated as the maximum of the individual cardinalities/amounts ', AllCounts)]]
    ;
      Result =.. [QueryWord, geq, MaxCount, Measure, []]
    ),
    Indices = AllIndices
  ;
    % there are aggregate solutions 
    find_maximal_count1(CountsIndices, 0, MaxCount, [], MaxIndices), 
    get_all_counts_and_indices(CountsIndices, AllCounts, _AllIndices),
    delete(AllCounts, MaxCount, RemainingCounts),
    (
      RemainingCounts \= [_]
      ->
      Result =.. [QueryWord, geq, MaxCount, Measure, [text('calculated as the sum of the individual cardinalities/amounts ', RemainingCounts)]]
    ;
      Result =.. [QueryWord, geq, MaxCount, Measure, []]
    ),
    Indices = MaxIndices
  ).

find_maximal_count1([], MaxCount, MaxCount, Indices, Indices).

find_maximal_count1([(Count1, Indices1)|CountsIndices], CountSoFar, MaxCount, IndicesSoFar, Indices) :-
  (
    Count1 > CountSoFar
    ->
    find_maximal_count1(CountsIndices, Count1, MaxCount, Indices1, Indices)
   ;
    find_maximal_count1(CountsIndices, CountSoFar, MaxCount, IndicesSoFar, Indices)
  ).

get_all_counts_and_indices(CountsIndices, Counts, Indices) :-
  get_all_counts_and_indices(CountsIndices, [], RawCounts, [], RawIndices),
  % sort counts
  sort(RawCounts, Counts),
  flatten(RawIndices, FlattenedRawIndices),
  sort(FlattenedRawIndices, Indices).
  
get_all_counts_and_indices([], Counts, Counts, RawIndices, RawIndices).

get_all_counts_and_indices([(Count, Index)|CountsIndices], CountsSoFar, Counts, RawIndicesSoFar, RawIndices) :-
  get_all_counts_and_indices(CountsIndices, [Count|CountsSoFar], Counts, [Index|RawIndicesSoFar], RawIndices).


%---------------------------------------------------------------------------------------------------------
%
%  copula
%
%  in fol_to_clauses the transitive copula has been marked
%
%    - as be_MOD if it is adorned with modifiers
%
%    - as be_ID if it conjoins two proper names without modifiers
%
%    - as be_NP if it conjoins two noun phrases – at least one of which is not a proper name – without 
%      modifiers
%
%    - as be_ADJ if it conjoins a noun phrase with an intransitive predicative adjective
%
%  to allow deductions with the help of a small number of auxiliary axioms
%
%---------------------------------------------------------------------------------------------------------
/*
% axiom c2 for attributive adjectives
% object(A1) & be_NP(A1,A2) & property(A2) |- property(A1)
% example: Every red cat is an animal. John is a red cat. |- John is an animal.
% note: this example works also with Prolog axiom transitivity_NP
% note: axiom deactivated since it allows the wrong deduction of
% John is a good husband and is a bad father. |- John is a good father.
prolog_axiom_text(c2, 'Prolog Axiom c2: Identity of attributive adjectives.').
prolog_axiom(property(World, A1, Adjective, Degree), _IndicesSoFar, [prolog_axiom(c2)|Indices]) :-
  exists_asserted_atom(object(World, A1, _B1, _T1, na, _EQ1, _N1), Indices1),
  exists_asserted_atom(predicate(World, _I, be_NP, A1, A2), Indices2),
  exists_asserted_atom(property(World, A2, Adjective, Degree), Indices3),
  append([Indices1, Indices2, Indices3], Indices123),
  sort(Indices123, Indices).
*/

% axiom c3 for intransitive predicative adjectives
% object(A1) & be_ADJ(A1,A2) & property(A2) |- property(A1)
% example: A man who is tired sleeps. |- A tired man sleeps.
prolog_axiom_text(c3, 'Prolog Axiom c3: Identity of intransitive predicative adjectives.').
prolog_axiom(property(World, A1, Adjective, Degree), _IndicesSoFar, [prolog_axiom(c3)|Indices]) :-
  % auxiliary axiom should not be used if the theorem also contains "... is tired ..."
  clauses(Clauses),
  member(satchmo_clause(Body, Head, [theorem(_)|_]), Clauses), 
  \+ subterm(predicate(World, _Ref, be_ADJ, _Obj, A1), Body),
  \+ subterm(predicate(World, _Ref, be_ADJ, _Obj, A1), Head),
  exists_asserted_atom(object(World, A1, _B1, _T1, _Measure, _EQ1, _N1), Indices1),
  exists_asserted_atom(predicate(World, _I, be_ADJ, A1, A2), Indices2), 
  exists_asserted_atom(property(World, A2, Adjective, Degree), Indices3),
  append([Indices1, Indices2, Indices3], Indices123),
  sort(Indices123, Indices).

% axiom c4 for objects and intransitive predicative adjectives
% object1(A1) & be_NP(A1,A2) & object2(A2) & be_ADJ(A1,A3) & property(A3) |- property(A2)
% example: Every cat is an animal. A cat is red. |- An animal is red.
prolog_axiom_text(c4, 'Prolog Axiom c4: Identity of objects and intransitive predicative adjectives.').
prolog_axiom(property(World, A2, Adjective, Degree), _IndicesSoFar, [prolog_axiom(c4)|Indices]) :-
  exists_asserted_atom(object(World, A1, _B1, _T1, na, _EQ1, _N1), Indices1),
  exists_asserted_atom(predicate(World, _I1, be_NP, A1, A2), Indices2), 
  exists_asserted_atom(object(World, A2, _B2, _T2, na, _EQ2, _N2), Indices3), 
  exists_asserted_atom(predicate(World, _I2, be_ADJ, A1, A3), Indices4),
  exists_asserted_atom(property(World, A3, Adjective, Degree), Indices5),
  append([Indices1, Indices2, Indices3, Indices4, Indices5], Indices12345),
  sort(Indices12345, Indices).

% axiom c5 for copula combining proper names and/or somebody/something one of which is the subject of an intransitive verb
% examples: John sleeps. John is Mary. |- Mary sleeps.   
prolog_axiom_text(c5, 'Prolog Axiom c5: Identity of proper names and/or somebody/something one of which is subject of intransitive verb.').
prolog_axiom(predicate(World, I2, Verb, A2), _IndicesSoFar, [prolog_axiom(c5)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_ID, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_ID, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, Verb, A1), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).
 
% axiom c6 for copula combining proper names and/or somebody/something one of which is the subject of a transitive verb
% examples: John sees a man. John is Mary. |- Mary sees a man. 
prolog_axiom_text(c6, 'Prolog Axiom c6: Identity of proper names and/or somebody/something one of which is subject of transitive verb.').
prolog_axiom(predicate(World, I2, Verb, A2, A3), _IndicesSoFar, [prolog_axiom(c6)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_ID, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_ID, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, Verb, A1, A3), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).

% axiom c7 for copula combining proper names and/or somebody/something one of which is the object of a transitive verb
% examples: A man sees John. John is Mary. |- A man sees Mary.   
prolog_axiom_text(c7, 'Prolog Axiom c7: Identity of proper names and/or somebody/something one of which is object of transitive verb.').
prolog_axiom(predicate(World, I2, Verb, A3, A2), _IndicesSoFar, [prolog_axiom(c7)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_ID, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_ID, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, Verb, A3, A1), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).
  
% axiom c8 for copula combining proper names and/or somebody/something one of which is the subject of a ditransitive verb
% examples: John gives a card to a clerk. John is Mary. |- Mary gives a card to a clerk.   
prolog_axiom_text(c8, 'Prolog Axiom c8: Identity of proper names and/or somebody/something one of which is subject of ditransitive verb.').
prolog_axiom(predicate(World, I2, Verb, A2, A3, A4), _IndicesSoFar, [prolog_axiom(c8)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_ID, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_ID, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, Verb, A1, A3, A4), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).
  
% axiom c9 for copula combining proper names and/or somebody/something one of which is the direct object of a ditransitive verb
% examples: A man gives John to a clerk. John is Mary. |- A man gives Mary to a clerk.   
prolog_axiom_text(c9, 'Prolog Axiom c9: Identity of proper names and/or somebody/something one of which is direct object of ditransitive verb.').
prolog_axiom(predicate(World, I2, Verb, A3, A2, A4), _IndicesSoFar, [prolog_axiom(c9)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_ID, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_ID, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, Verb, A3, A1, A4), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).
  
% axiom c10 for copula combining proper names and/or somebody/something one of which is the indirect object of a ditransitive verb
% examples: A man gives a card to John. John is Mary. |- A man gives a card to Mary.   
prolog_axiom_text(c10, 'Prolog Axiom c10: Identity of proper names and/or somebody/something one of which is indirect object of ditransitive verb.').
prolog_axiom(predicate(World, I2, Verb, A3, A4, A2), _IndicesSoFar, [prolog_axiom(c10)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_ID, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_ID, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, Verb, A3, A4, A1), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).

% axiom c11 for identity of subjects of intransitive verbs
% object1(A1) & object2(A2) & be_NP(A1,A2) & intransitive_verb(A1) |- intransitive_verb(A2)
% example: A father of Mary dances. He is a relative of Mary. |- A relative of Mary dances.
prolog_axiom_text(c11, 'Prolog Axiom c11: Identity of subjects of intransitive verbs.').
prolog_axiom(predicate(World, I2, IntransitiveVerb, A2), _IndicesSoFar, [prolog_axiom(c11)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_NP, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_NP, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, IntransitiveVerb, A1), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).

% 20110506: note that c12 and c13 are also taken care of by fol_to_clauses/interpret_copula_with_numbers
% axiom c12 for identity of subjects of transitive verbs
% object1(A1) & object2(A2) & be_NP(A1,A2) & transitive_verb(A1,A3) |- transitive_verb(A2,A3)
% example: A girl is a scholar. The girl reads a book. |- A scholar reads a book.
prolog_axiom_text(c12, 'Prolog Axiom c12: Identity of subjects of transitive verbs.').
prolog_axiom(predicate(World, I2, TransitiveVerb, A2, A3), _IndicesSoFar, [prolog_axiom(c12)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_NP, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_NP, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, TransitiveVerb, A1, A3), Indices2),
  \+ TransitiveVerb = be, 
  \+ TransitiveVerb = be_NP, 
  \+ TransitiveVerb = be_MOD, 
  \+ TransitiveVerb = be_ID, 
  \+ TransitiveVerb = be_ADJ,
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices). 

% axiom c13 for identity of objects of transitive verbs
% object1(A1) & object2(A2) & be_NP(A1,A2) & transitive_verb(A3,A1) |- transitive_verb(A3,A2)
% example: A girl is a scholar. A teacher sees the girl. |- A teacher sees a scholar.
prolog_axiom_text(c13, 'Prolog Axiom c13: Identity of objects of transitive verbs.').
prolog_axiom(predicate(World, I2, TransitiveVerb, A3, A2), _IndicesSoFar, [prolog_axiom(c13)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_NP, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_NP, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, TransitiveVerb, A3, A1), Indices2),
  \+ TransitiveVerb = be, 
  \+ TransitiveVerb = be_NP, 
  \+ TransitiveVerb = be_MOD, 
  \+ TransitiveVerb = be_ID, 
  \+ TransitiveVerb = be_ADJ,
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).

% axiom c14 for identity of subjects of ditransitive verbs
% object1(A1) & object2(A2) & be_NP(A1,A2) & ditransitive_verb(A1,A3,A4) |- ditransitive_verb(A2,A3,A4)
% example: A girl is a scholar. The girl gives a teacher a book. |- A scholar gives a teacher a book.
prolog_axiom_text(c14, 'Prolog Axiom c14: Identity of subjects of ditransitive verbs.').
prolog_axiom(predicate(World, I2, DitransitiveVerb, A2, A3, A4), _IndicesSoFar, [prolog_axiom(c14)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_NP, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_NP, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, DitransitiveVerb, A1, A3, A4), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).
  
% axiom c15 for identity of direct objects of ditransitive verbs
% object1(A1) & object2(A2) & be_NP(A1,A2) & ditransitive_verb(A3,A1,A4) |- ditransitive_verb(A3,A2,A4)
% example: A book is an item. A girl gives a teacher the book. |- A girl gives a teacher an item.
prolog_axiom_text(c15, 'Prolog Axiom c15: Identity of direct objects of ditransitive verbs.').
prolog_axiom(predicate(World, I2, DitransitiveVerb, A3, A2, A4), _IndicesSoFar, [prolog_axiom(c15)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_NP, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_NP, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, DitransitiveVerb, A3, A1, A4), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).
  
% axiom c16 for identity of indirect objects of ditransitive verbs
% object1(A1) & object2(A2) & be_NP(A1,A2) & ditransitive_verb(A3,A4,A1) |- ditransitive_verb(A3,A4,A2)
% example: A teacher is a lady. A girl gives the teacher a book. |- A girl gives a lady a book.
prolog_axiom_text(c16, 'Prolog Axiom c16: Identity of indirect objects of ditransitive verbs.').
prolog_axiom(predicate(World, I2, DitransitiveVerb, A3, A4, A2), _IndicesSoFar, [prolog_axiom(c16)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_NP, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_NP, A2, A1), Indices1)
  ),
  exists_asserted_atom(predicate(World, I2, DitransitiveVerb, A3, A4, A1), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).

/* 
% 31 Jan 2021: deactivated since it leads to infinite loop with recursion
% axiom c17 for identity of of-relations
% but: axiom c1c can be used instead
% object1(A1) & object2(A2) & object2(A3) & be_NP(A1,A2) & of-relation(A3,A1) |- of-relation(A3,A2)
% example: Mary is a person. Mary's dog barks. |- A person's dog barks.
prolog_axiom_text(c17, 'Prolog Axiom c17: Identity of of-relation.').
prolog_axiom(relation(World, A3, Noun, of, A2), _IndicesSoFar, [prolog_axiom(c17)|Indices]) :-
  (
    exists_asserted_atom(predicate(World, _I1, be_NP, A1, A2), Indices1) 
    -> 
    true
  ; 
    exists_asserted_atom(predicate(World, _I1, be_NP, A2, A1), Indices1)
  ),
  exists_asserted_atom(relation(World, A3, Noun, of, A1), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).
*/

% axiom c18 for replacing the referent of a class by the referent of one of its members
% example: Every fox is an animal. The class 'animal' gets the referent of its member 'fox'.
% excerpt from steamroller:
% Every fox is an animal. Every bird is an animal. There is a fox. There is a bird. 
% Every animal A eats every animal D that is smaller than A and eats a plant. Every bird is smaller than every fox. 
% |- A fox eats a bird.
prolog_axiom_text(c18, 'Prolog Axiom c18: Class referent is replaced by the referent of a member.').
prolog_axiom(object(World, RefMember, Class, countable, na, geq, 1), _IndicesSoFar, [prolog_axiom(c18)|Indices]) :-
  exists_asserted_atom(object(World,RefMember,_Member,countable,na,geq,1), Indices1),
  exists_asserted_atom(predicate(World,RefBe,be_NP,RefMember,RefClass), Indices2),
  subterm(RefMember, RefClass), 
  subterm(RefMember, RefBe), 
  exists_asserted_atom(object(World,RefClass,Class,countable,na,geq,1), Indices2),  
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).


%---------------------------------------------------------------------------------------------------------
%
%  axioms for equality 
%
%    - reflexivity
%    - symmetry
%    - transitivity
%
%---------------------------------------------------------------------------------------------------------

/*
% This section can be replaced by the simpler one below that directly covers reflexivity, symmetry and 
% transitivity of the copula forms be_NP and be_ID. However, currently the grocer example needs 
% additionally c1c.

% axiom s0_ID for equality of proper names (reflexivity)
% examples: John is John.
% failing examples: John is not John.
prolog_axiom_text(s0_ID, 'Prolog Axiom s0_ID: Every proper name is identical to itself, to somebody or to something.').
prolog_axiom(predicate(_World, _, be_ID, A, A), _IndicesSoFar, [prolog_axiom(s0_ID)]).

% axiom s0_NP for equality of objects (reflexivity)
% examples: A man is the man. Some water is the water.
% failing examples: A man is not the man. Some water is not the water.
prolog_axiom_text(s0_NP, 'Prolog Axiom s0_NP: Everything is identical to itself.').
prolog_axiom(predicate(_World, _, be_NP, A, A), _IndicesSoFar, [prolog_axiom(s0_NP)]).

% axiom c0cc for objects and symmetric copula
% object1(A1) & be_NP(A1,A2) & object2(A2) |- object1(A2) & be_NP(A2,A1) & object2(A1) 
% example: A manager is a man. |- A man is a manager.
prolog_axiom_text(c0cc, 'Prolog Axiom c0cc: Identity of objects.').
prolog_axiom(predicate(World, I, be_NP, A2, A1), _IndicesSoFar, [prolog_axiom(c0cc)|Indices]) :-
  exists_asserted_atom(predicate(World, I, be_NP, A1, A2), Indices1),
  exists_asserted_atom(object(World, A1, _B1, _T1, na, _EQ1, _N1), Indices2),
  exists_asserted_atom(object(World, A2, _B2, _T2, na, _EQ2, _N2), Indices3),
  append([Indices1, Indices2, Indices3], Indices123),
  sort(Indices123, Indices).

% axiom c0ci1 for objects, integers and symmetric copula
% be_NP(A1,A2) |- be_NP(A2,A1) where one of A1 and A2 is an integer
% example: 3 is an integer. |- An integer is 3. 
prolog_axiom_text(c0ci1, 'Prolog Axiom c0ci1: Identity of integers.').
prolog_axiom(predicate(World, I, be_NP, A, int(Integer)), _IndicesSoFar, [prolog_axiom(c0ci1)|Indices]) :-
  exists_asserted_atom(predicate(World, I, be_NP, int(Integer), A), Indices).
  
% axiom c0ci2 for objects, integers and symmetric copula
% be_NP(A1,A2) |- be_NP(A2,A1) where one of A1 and A2 is an integer
% example: An integer is 3. |- 3 is an integer.
prolog_axiom_text(c0ci2, 'Prolog Axiom c0ci2: Identity of integers.').
prolog_axiom(predicate(World, I, be_NP, int(Integer), A), _IndicesSoFar, [prolog_axiom(c0ci2)|Indices]) :-
  exists_asserted_atom(predicate(World, I, be_NP, A, int(Integer)), Indices).
  
% axiom c0cr1 for objects, reals and symmetric copula
% be_NP(A1,A2) |- be_NP(A2,A1) where one of A1 and A2 is a real
% example: A real is 3.14. |- 3.14 is a real.
prolog_axiom_text(c0cr1, 'Prolog Axiom c0cr1: Identity of reals.').
prolog_axiom(predicate(World, I, be_NP, A, real(Real)), _IndicesSoFar, [prolog_axiom(c0cr1)|Indices]) :-
  exists_asserted_atom(predicate(World, I, be_NP, real(Real), A), Indices).
  
% axiom c0cr2 for objects, reals and symmetric copula
% be_NP(A1,A2) |- be_NP(A2,A1) where one of A1 and A2 is a real
% example: A real is 3.14. |- 3.14 is a real.
prolog_axiom_text(c0cr2, 'Prolog Axiom c0cr2: Identity of reals.').
prolog_axiom(predicate(World, I, be_NP, real(Real), A), _IndicesSoFar, [prolog_axiom(c0cr2)|Indices]) :-
  exists_asserted_atom(predicate(World, I, be_NP, A, real(Real)), Indices).

% axiom c0cp for countable and named objects and symmetric copula
% object1(A1) & be_NP(A1,A2) & object2(A2) |- object1(A2) & be_NP(A2,A1) & object2(A1) 
% example: A man is John. |- John is a man.
prolog_axiom_text(c0cp, 'Prolog Axiom c0cp: Identity of countable and named objects.').
prolog_axiom(predicate(World, I, be_NP, A2, A1), _IndicesSoFar, [prolog_axiom(c0cp)|Indices]) :-
  exists_asserted_atom(predicate(World, I, be_NP, A1, A2), Indices1),
  exists_asserted_atom(object(World, A1, _B1, _T1, na, _EQ1, _N1), Indices2),
  exists_asserted_atom(object(World, A2, _Name, named, na, _EQ2, _N2), Indices3),
  append([Indices1, Indices2, Indices3], Indices123),
  sort(Indices123, Indices).

% axiom c0pc1 for named and countable objects and symmetric copula
% object1(A1) & be_NP(A1,A2) & object2(A2) |- object1(A2) & be_NP(A2,A1) & object2(A1) 
% example: John is a man. |- A man is John.
prolog_axiom_text(c0pc1, 'Prolog Axiom c0pc1: Identity of named and countable objects.').
prolog_axiom(predicate(World, I, be_NP, A2, A1), _IndicesSoFar, [prolog_axiom(c0pc)|Indices]) :-
  exists_asserted_atom(predicate(World, I, be_NP, A1, A2), Indices1),
  exists_asserted_atom(object(World, A1, _Name, named, na, _EQ1, _N1), Indices2),
  exists_asserted_atom(object(World, A2, _B2, _T2, na, _EQ2, _N2), Indices3),
  append([Indices1, Indices2, Indices3], Indices123),
  sort(Indices123, Indices).

% axiom c0pc2 for named and countable objects and symmetric copula
% object1(A1) & be_NP(A1,A2) & object2(A2) |- object2(A1) 
% example: France is a country. France is large. |- A country is large. (assign country the referent of France)
prolog_axiom_text(c0pc2, 'Prolog Axiom c0pc2: Identity of named and countable objects.').
prolog_axiom(object(World, A1, B2, countable, na, EQ2, N2), _IndicesSoFar, [prolog_axiom(c0pc2)|Indices]) :-
  exists_asserted_atom(predicate(World, _I, be_NP, A1, A2), Indices1),
  exists_asserted_atom(object(World, A1, _B1, named, na, _EQ1, _N1), Indices2), 
  exists_asserted_atom(object(World, A2, B2, countable, na, EQ2, N2), Indices3),
  append([Indices1, Indices2, Indices3], Indices123),
  sort(Indices123, Indices).
*/


% auxiliary axioms for copula
% section replaces section above
% currently c1c is still needed for Grocer example

% axiom for reflexivity of copula for proper names
% example: John is John.
% failing example: John is not John.
prolog_axiom_text(reflexivity_ID, 'Prolog Axiom reflexivity_ID: Reflexivity of copula for proper names.').
prolog_axiom(predicate(_World, sk, be_ID, A, A), _IndicesSoFar, [prolog_axiom(reflexivity_ID)]) :-
  % introduce new skolem constant sk
  nonvar(A).

/* 
% 31 Jan 2021: deactivated since it leads to infinite loops with recursion
% axiom for reflexivity of copula for objects
% examples: A man is the man. Some water is the water.
% failing examples: A man is not the man. Some water is not the water.
prolog_axiom_text(reflexivity_NP, 'Prolog Axiom reflexivity_NP: Reflexivity of copula for objects.').
prolog_axiom(predicate(_World, sk, be_NP, A, A), IndicesSoFar, [prolog_axiom(reflexivity_NP)]) :-
  % introduce new skolem constant sk
  % exclude the case that the query 'Which ... is XYZ?' results in the answer substitution 'which = XYZ'
  \+ member(prolog_axiom(w14), IndicesSoFar), 
  \+ member(prolog_axiom(w15), IndicesSoFar),
  nonvar(A).
*/

% axiom for symmetry of copula for proper names
% example: Johnny is John. |- John is Johnny.
prolog_axiom_text(symmetry_ID, 'Prolog Axiom symmetry_ID: Symmetry of copula for proper names.').
prolog_axiom(predicate(_World, Ref_AB, be_ID, A, B), _IndicesSoFar, [prolog_axiom(symmetry_ID)|Indices]) :-
  nonvar(A), 
  nonvar(B),
  exists_asserted_atom(predicate(_World, Ref_AB, be_ID, B, A), Indices).

% axiom for symmetry of copula for objects
% example: A man is John. |- John is a man.
% example: A man is a manager. |- A manager is a man.
prolog_axiom_text(symmetry_NP, 'Prolog Axiom symmetry_NP: Symmetry of copula for objects.').
prolog_axiom(predicate(_World, Ref_AB, be_NP, A, B), _IndicesSoFar, [prolog_axiom(symmetry_NP)|Indices]) :-
  nonvar(A), 
  nonvar(B),
  exists_asserted_atom(predicate(_World, Ref_AB, be_NP, B, A), Indices).

% axiom for transitivity of copula for proper names
% example: Johnny is John. John is Joe. |- Johnny is Joe.
prolog_axiom_text(transitivity_ID, 'Prolog Axiom transitivity_ID: Transitivity of copula for proper names.').
prolog_axiom(predicate(_World, Ref_AB, be_ID, A, C), _IndicesSoFar, [prolog_axiom(transitivity_ID)|Indices]) :-
  nonvar(A), 
  nonvar(C),
  exists_asserted_atom(predicate(_World, Ref_AB, be_ID, A, B), Indices1),
  exists_asserted_atom(predicate(_World, _, be_ID, B, C), Indices2),
  append(Indices1, Indices2, Indices).

% axiom for transitivity of copula for objects
% example: A man is John. John is a manager. |- A man is a manager.
prolog_axiom_text(transitivity_NP, 'Prolog Axiom transitivity_NP: Transitivity of copula for objects.').
prolog_axiom(predicate(_World, Ref_AB, be_NP, A, C), _IndicesSoFar, [prolog_axiom(transitivity_NP)|Indices]) :-
  nonvar(A), 
  nonvar(C),
  exists_asserted_atom(predicate(_World, Ref_AB, be_NP, A, B), Indices1),
  (exists_asserted_atom(predicate(_World, _, be_NP, B, C), Indices2) ; exists_asserted_atom(predicate(_World, _, be_NP, C, B), Indices2)),
  append(Indices1, Indices2, Indices).

% axiom c1c for identity of countable objects
% be_NP(A1,A2) & Noun(A1) |- Noun(A2) where Noun(A2) can have a smaller count
% example: Three  foxes are red. Every fox is an animal. |- (At least) two  animals are red.
% necessary for grocer example
prolog_axiom_text(c1c, 'Prolog Axiom c1c: Identity of countable objects.').
prolog_axiom(object(World, A2, Noun, countable, na, EQ, N2), _IndicesSoFar, [prolog_axiom(c1c)|Indices]) :-
  nonvar(EQ), nonvar(N2),
  exists_asserted_atom(predicate(World, _Ref, be_NP, A2, A1), Indices),
  exists_asserted_atom(object(World, A1, Noun, countable, na, EQ, N1), Indices),
  N1 >= N2.

% axiom c1m for identity of mass objects
% be_NP(A1,A2) & Noun(A2) |- Noun(A1)
prolog_axiom_text(c1m, 'Prolog Axiom c1m: Identity of mass objects.').
prolog_axiom(object(World, A1, Noun, mass, na, na, na), _IndicesSoFar, [prolog_axiom(c1m)|Indices]) :-
  exists_asserted_atom(predicate(World, _Ref, be_NP, A1, A2), Indices),
  exists_asserted_atom(object(World, A2, Noun, mass, na, na, na), Indices).

/* 
%---------------------------------------------------------------------------------------------------------
%
%  axioms for the combination of roles of proper names
%  questionnable axioms
%  not adapted to current representation of proper names
%
%---------------------------------------------------------------------------------------------------------

% axiom cr1 for the combination of roles of a proper name
% name(Name) & be_NP(Name,SK1) & be_NP(Name,SK2) |- be_NP(SK1,SK2)
% example: John is a man. John is a woman. |- A man is a woman. 
prolog_axiom_text(cr1, 'Prolog Axiom cr1: Combination of roles of a proper name.').
prolog_axiom(predicate(World, _Referent, be_NP, SK1, SK2), _IndicesSoFar, [prolog_axiom(cr1)|Indices]) :-
  exists_asserted_atom(predicate(World, _Referent1, be_NP, named(Name), SK1), Indices1),
  exists_asserted_atom(predicate(World, _Referent2, be_NP, named(Name), SK2), Indices2),
  append(Indices1, Indices2, Indices12),
  sort(Indices12, Indices).  
  
% axiom cr2 for the combination of roles of proper names
% be_ID(Name1,Name2) & be_NP(Name1,SK1) & be_NP(Name2,SK2) |- be_NP(SK1,SK2)
% example: John is Mary. John is a man. Mary is a woman. |- A man is a woman. 
prolog_axiom_text(cr2, 'Prolog Axiom cr2: Combination of roles of proper names.').
prolog_axiom(predicate(World, _Referent, be_NP, SK1, SK2), _IndicesSoFar, [prolog_axiom(cr2)|Indices]) :-
  exists_asserted_atom(predicate(World, _Referent1, be_ID, named(Name1), named(Name2)), Indices1),
  (
    exists_asserted_atom(predicate(World, _Referent2, be_NP, named(Name1), SK1), Indices2),
    exists_asserted_atom(predicate(World, _Referent3, be_NP, named(Name2), SK2), Indices3)
    ->
    true
  ;
    exists_asserted_atom(predicate(World, _Referent2, be_NP, named(Name1), SK2), Indices2),
    exists_asserted_atom(predicate(World, _Referent3, be_NP, named(Name2), SK1), Indices3)
  ),
  append([Indices1, Indices2, Indices3], Indices123),
  sort(Indices123, Indices).
*/


%---------------------------------------------------------------------------------------------------------
%
%  deductions from  plurals
%  
%  APE ensures that all cardinalities are natural numbers, unless used with measurement nouns
%
%  "Count Noun" is represented by "at least Count Noun" (see drs_to_fol)
%
%  "less than Count Noun" is represented by "not at least Count Noun" (see drs_to_fol)
%
%  "at most Count Noun" is represented by "not more than Count Noun" (see drs_to_fol)
%
%---------------------------------------------------------------------------------------------------------

% enable deductions from distributive plurals 
% for distributive plurals only
prolog_axiom_text(cd0, 'Prolog Axiom cd0: enable deductions from distributive plurals').
prolog_axiom(has_part(World, A, _Part), _IndicesSoFar, [prolog_axiom(cd0)|Indices]) :-
  % referent A is a distributive plural in any syntactic role
  exists_asserted_atom(object(World, A, _B, _C, na, _EQ, M), Indices),
  M>1,
  user:clauses(Clauses),
  member(satchmo_clause(Body, _Head, Indices), Clauses),
  support:subterm(has_part(World, A, _Part), Body),
  !.

% each of M objects |- each of M-1, ..., each of 2 objects, 1 object
% for distributive plurals only
% removing the lines in parentheses below will also activate this auxiliary axiom for collective plurals
prolog_axiom_text(cd1, 'Prolog Axiom cd1: each of M objects |- each of M-1, ..., each of 2 objects, 1 object').
prolog_axiom(object(World, A, B, C, D, geq, N), _IndicesSoFar, [prolog_axiom(cd1)|Indices]) :-
  nonvar(N), 
  N>=1,
  exists_asserted_atom(object(World, A, B, C, D, geq, M), Indices),
  M>1,
  N<M,
  % referent A is a distributive plural in any syntactic role
  user:clauses(Clauses),
  (
    member(satchmo_clause(Body, _Head, Indices), Clauses),
    support:subterm(has_part(World, A, _Part), Body)
  ;
    % Each of 2 men and 3 women waits.  |- Two women wait.
    member(satchmo_clause(has_part(World, _Whole, A), _Head, Indices), Clauses)
  ),
  !.
  
/*
% M objects |- at least 1, 2, ..., M objects
prolog_axiom_text(cd2, 'Prolog Axiom cd2: M objects |- at least 1, 2, ..., M objects').
prolog_axiom(object(World, A, B, C, na, geq, N), _IndicesSoFar, [prolog_axiom(cd2)|Indices]) :-
  nonvar(N),
  exists_asserted_atom(object(World, A, B, C, na, eq, M), Indices),
  M>1,
  N=<M.
  
% M objects |- more than 1, 2, ..., M-1 objects
prolog_axiom_text(cd3, 'Prolog Axiom cd3: M objects |- more than 1, 2, ..., M-1 objects').
prolog_axiom(object(World, A, B, C, na, greater, N), _IndicesSoFar, [prolog_axiom(cd3)|Indices]) :-
  nonvar(N),
  exists_asserted_atom(object(World, A, B, C, na, eq, M), Indices),
  M>1,
  N<M.

% at least M objects |- M, M-1, ..., 1 objects
% for distributive plurals only
% removing the lines in parentheses below will also activate this auxiliary axiom for collective plurals
prolog_axiom_text(cd4, 'Prolog Axiom cd4: at least M objects |- M, M-1, ..., 1 objects').
prolog_axiom(object(World, A, B, C, na, eq, N), _IndicesSoFar, [prolog_axiom(cd4)|Indices]) :-
  nonvar(N),
  exists_asserted_atom(object(World, A, B, C, na, geq, M), Indices),
  M>=1,
  N=<M,
  % referent A is a distributive plural in any syntactic role
  user:clauses(Clauses),
  (
    member(satchmo_clause(Body, _Head, Indices), Clauses),
    support:subterm(has_part(World, A, _Part), Body)
  ;
    % Each of 2 men and 3 women waits.  |- Two women wait.
    member(satchmo_clause(has_part(World, _Whole, A), _Head, Indices), Clauses)
  ),
  !.
*/

% at least M objects |- at least 1, 2, ..., M-1 objects
prolog_axiom_text(cd5, 'Prolog Axiom cd5: at least M objects |- at least 1, 2, ..., M-1 objects').
prolog_axiom(object(World, A, B, C, na, geq, N), _IndicesSoFar, [prolog_axiom(cd5)|Indices]) :-
  nonvar(N),
  exists_asserted_atom(object(World, A, B, C, na, geq, M), Indices),
  M>=1,
  N<M.

% at least M objects |- more than 1, 2, ..., M-1 objects
prolog_axiom_text(cd6, 'Prolog Axiom cd6: at least M objects |- more than 1, 2, ..., M-1 objects').
prolog_axiom(object(World, A, B, C, na, greater, N), _IndicesSoFar, [prolog_axiom(cd6)|Indices]) :-
  nonvar(N),
  exists_asserted_atom(object(World, A, B, C, na, geq, M), Indices),
  M>=1,
  N<M.

/*
% more than M objects |- M+1, M, M-1, ..., 1 objects
% for distributive plurals only
% removing the lines in parentheses below will also activate this auxiliary axiom for collective plurals
prolog_axiom_text(cd7, 'Prolog Axiom cd7: more than M objects |- M+1, M, M-1, ..., 1 objects').
prolog_axiom(object(World, A, B, C, na, eq, N), _IndicesSoFar, [prolog_axiom(cd7)|Indices]) :-
  nonvar(N),
  exists_asserted_atom(object(World, A, B, C, na, greater, M), Indices),
  M>=1,
  N=<M+1,
  % referent A is a distributive plural in any syntactic role
  user:clauses(Clauses),
  (
    member(satchmo_clause(Body, _Head, Indices), Clauses),
    support:subterm(has_part(World, A, _Part), Body)
  ;
    % Each of 2 men and 3 women waits.  |- Two women wait.
    member(satchmo_clause(has_part(World, _Whole, A), _Head, Indices), Clauses)
  ),
  !.
*/

% more than M objects |- at least 1, 2, ..., M, M+1 objects
prolog_axiom_text(cd8, 'Prolog Axiom cd8: more than M objects |- at least 1, 2, ..., M+1 objects').
prolog_axiom(object(World, A, B, C, na, geq, N), _IndicesSoFar, [prolog_axiom(cd8)|Indices]) :-
  nonvar(N),
  exists_asserted_atom(object(World, A, B, C, na, greater, M), Indices),
  M>=1,
  N=<M+1.
    
% more than M objects |- more than 1, 2, ..., M-1 objects
prolog_axiom_text(cd9, 'Prolog Axiom cd9: more than M objects |- more than 1, 2, ..., M-1 objects').
prolog_axiom(object(World, A, B, C, na, greater, N), _IndicesSoFar, [prolog_axiom(cd9)|Indices]) :-
  nonvar(N),
  exists_asserted_atom(object(World, A, B, C, na, greater, M), Indices),
  M>=1,
  N<M.

% deduction from conjunctive plurals acting as direct objects of transitive verbs
% example: John has a pear and an apple. |- John has an apple.
% example that succeeds but should not succeed: John combines a part A and a part B. |- John combines a part A.
prolog_axiom_text(conjunctivepluraldirectobject1, 'Prolog Axiom conjunctivepluraldirectobject1').
prolog_axiom(predicate(World, _Ref, Verb, RefSubject, RefObject), _IndicesSoFar, [prolog_axiom(conjunctivepluraldirectobject1)|Indices]):-
  % transitive verb that has conjunctive plural as direct object
  exists_asserted_atom(predicate(World, _RefVerb, Verb, RefSubject, RefConjunction), Indices), 
  % conjunctive plural
  exists_asserted_atom(object(World, RefConjunction, na, countable, na, eq, 2), Indices),
  exists_asserted_atom(has_part(World, RefConjunction, RefObject), Indices), 
  % element of the conjunctive plural
  exists_asserted_atom(object(World, RefObject, _Object, countable, na, geq, 1), Indices). 

% deduction from conjunctive plurals acting as direct objects of ditransitive verbs
% example: John and Mary give an apple and a pear to Harry and Tom. |- John and Mary give an apple to Harry and Tom.
prolog_axiom_text(conjunctivepluraldirectobject2, 'Prolog Axiom conjunctivepluraldirectobject2').
prolog_axiom(predicate(World, _Ref, Verb, RefSubject, RefObject, IndirectObject), _IndicesSoFar, [prolog_axiom(conjunctivepluraldirectobject2)|Indices]):-
  % ditransitive verb that has conjunctive plural as direct object
  exists_asserted_atom(predicate(World, _RefVerb, Verb, RefSubject, RefConjunction, IndirectObject), Indices), 
  % conjunctive plural
  exists_asserted_atom(object(World, RefConjunction, na, countable, na, eq, 2), Indices),
  exists_asserted_atom(has_part(World, RefConjunction, RefObject), Indices), 
  % element of the conjunctive plural
  exists_asserted_atom(object(World, RefObject, _Object, countable, na, geq, 1), Indices). 


%---------------------------------------------------------------------------------------------------------
%
%  aggregation
%
%---------------------------------------------------------------------------------------------------------

% aggregation: check whether there at least a given number of solutions 
% fail if there are not at least two solutions (for one solution there are other auxiliary axioms)
% Count is an integer >1
% example: There is a cat. There is a dog. Every cat is an animal. Every dog is an animal. No cat is a dog. |- There are 2  animals.
% example: There is a cat. There is a dog. Every cat is an animal. Every dog is an animal. No cat is a dog. |- There are at least 2  animals.
prolog_axiom_text(agg1, 'Prolog Axiom agg1: aggregation for at least a given number of solutions').
prolog_axiom(object(World, _A, B, C, D, geq, Count), _IndicesSoFar, [prolog_axiom(agg1)|Indices]) :- 
  integer(Count), 
  Count > 1,
  % consider only the case of Noun unmodified by adjectives and relative phrases
  % get clause containing "object(World, Referent, B, C, D, geq, Count)"
  user:clauses(Clauses), 
  member(satchmo_clause(Body, _Head, _Index), Clauses),
  support:subterm(object(World, _Referent, B, C, D, geq, Count), Body),
  % find all solutions 
  findall((M, Indices), (exists_asserted_atom(object(World, _A1, B, C, D, geq, M), Indices), \+ member(prolog_axiom(_), Indices)), AllSolutions),
  %%%nl, write('AllSolutions '), write(AllSolutions),
  (
    % there are no solutions or there is just a single solution indicating that this Prolog axiom is not applicable
    (AllSolutions = [] ; AllSolutions = [_])
    ->
    fail
  ;
    % AllSolutions = [_|_]
    % there can be spurious solutions that have no leaf nodes or that omit nodes between leaf and root
    eliminate_spurious_solutions(AllSolutions, SolutionsWithLeafNodes),
    % check that remaining solutions are distinct
    (
      % solutions_are_pairwise_distinct/3 succeeds
      solutions_are_pairwise_distinct(SolutionsWithLeafNodes, Solutions, IndicesOfDistinction)
      -> 
      true
    ;
      % solutions_are_pairwise_distinct/3 fails
      % add_warning_message_once(summation, '', 'Summing the cardinalities of the classes is not possible since not all classes are distinct.', 'Consider adding axioms of the form "No A is a B."'),
      fail
    ),
    % sum individual solutions and collect indices
    aggregate_solutions(Solutions, IndicesOfDistinction, TotalCount, Indices),
    % TotalCount must at least be Count
    TotalCount >= Count 
  ).
  
% aggregation: check whether there are more than a given number of solutions
% example: There are two cats. There is a dog. Every cat is an animal. Every dog is an animal. No cat is a dog. |- There are more than 2 animals.
% example: There is a cat. There is a dog. Every cat is an animal. Every dog is an animal. No cat is a dog. |- There are more than 0 animals.
% example: There is a cat. There is a dog. Every cat is an animal. Every dog is an animal. No cat is a dog. |\- There are more than 2 animals.
prolog_axiom_text(agg2, 'Prolog Axiom agg2: aggregation for more than a given number of solutions').
prolog_axiom(object(World, _A, B, C, D, greater, Count), _IndicesSoFar, [prolog_axiom(agg2)|Indices]) :- 
  integer(Count), 
  % consider only the case of Noun unmodified by adjectives and relative phrases
  % get clause containing "object(World, Referent, B, C, D, greater, Count)"
  user:clauses(Clauses), 
  member(satchmo_clause(Body, _Head, _Index), Clauses),
  support:subterm(object(World, _Referent, B, C, D, greater, Count), Body),
  % find all solutions 
  findall((M, Indices), (exists_asserted_atom(object(World, _A1, B, C, D, geq, M), Indices), \+ member(prolog_axiom(_), Indices)), AllSolutions),
  %%%nl, write('AllSolutions '), write(AllSolutions),
  (
    % there are no solutions or there is just a single solution indicating that this Prolog axiom is not applicable
    (AllSolutions = [] ; AllSolutions = [_])
    ->
    fail
  ;
    % AllSolutions = [_|_]
    % there can be spurious solutions that have no leaf nodes or that omit nodes between leaf and root
    eliminate_spurious_solutions(AllSolutions, SolutionsWithLeafNodes),
    % check that remaining solutions are distinct
    (
      % solutions_are_pairwise_distinct/3 succeeds
      solutions_are_pairwise_distinct(SolutionsWithLeafNodes, Solutions, IndicesOfDistinction)
      -> 
      true
    ;
      % solutions_are_pairwise_distinct/3 fails
      % add_warning_message_once(summation, '', 'Summing the cardinalities of the classes is not possible since not all classes are distinct.', 'Consider adding axioms of the form "No A is a B."'),
      fail
    ),
    % sum individual solutions and collect indices
    aggregate_solutions(Solutions, IndicesOfDistinction, TotalCount, Indices),
    % TotalCount must at least be Count
    TotalCount > Count 
  ). 

aggregation(Referent, Body, Count, Indices) :- 
  var(Count), 
  support:subterm(object(_World, Referent, Noun, Class, Measure, geq, _), Body),
  findall((M, Indices), 
          (
            exists_asserted_atom(object(_World, Referent, Noun, Class, Measure, geq, M), Indices), 
            \+ member(prolog_axiom(_), Indices), 
            satchmo:prove_body(Body, [], [], _) 
          ), 
          AllSolutions),
  %%%nl, write('AllSolutions '), write(AllSolutions),
  % there can be spurious solutions
  eliminate_spurious_solutions(AllSolutions, UniqueSolutions),
  (
    % there are no solutions or there is just a single solution indicating that aggregation is not applicable
    (UniqueSolutions = [] ; UniqueSolutions = [_])
    ->
    fail
  ;
    % UniqueSolutions = [_|_]
    % check that solutions are distinct
    (
      % solutions_are_pairwise_distinct/3 succeeds
      solutions_are_pairwise_distinct(UniqueSolutions, Solutions, IndicesOfDistinction)
      -> 
      true
    ;
      % solutions_are_pairwise_distinct/3 fails
      % add_warning_message_once(summation, '', 'Summing the cardinalities of the classes is not possible since not all classes are distinct.', 'Consider adding axioms of the form "No A is a B."'),
      fail
    ),
    % sum individual solutions and collect indices
    aggregate_solutions(Solutions, IndicesOfDistinction, Count, Indices)
  ).    


eliminate_spurious_solutions(Solutions, SolutionsWithLeafNodes) :-
  eliminate_spurious_solutions(Solutions, [], SolutionsWithLeafNodes).

eliminate_spurious_solutions([], SolutionsWithLeafNodes, SolutionsWithLeafNodes).

eliminate_spurious_solutions([(M, Indices1)|MoreSolutions], SoFar, SolutionsWithLeafNodes) :-
  (
    % there is a solution with the same cardinality and a proper superset of the indices
    member((M, Indices2), MoreSolutions),
    subset(Indices1, Indices2)
    ->
    eliminate_spurious_solutions(MoreSolutions, SoFar, SolutionsWithLeafNodes)
  ;
    select((M, Indices2), MoreSolutions, RestSolutions),
    subset(Indices2, Indices1)
    ->
    eliminate_spurious_solutions(RestSolutions, [(M, Indices1)|SoFar], SolutionsWithLeafNodes)
  ;
    % there is no solution with the same cardinality and a proper superset of the indices
    eliminate_spurious_solutions(MoreSolutions, [(M, Indices1)|SoFar], SolutionsWithLeafNodes)
  ).


solutions_are_pairwise_distinct(RawSolutions, Solutions, IndicesOfDistinction) :-
  solutions_are_pairwise_distinct(RawSolutions, [], Solutions, [], IndicesOfDistinction).

solutions_are_pairwise_distinct([], Solutions, Solutions, IndicesOfDistinction, IndicesOfDistinction).
  
solutions_are_pairwise_distinct([(M1, Indices1)|MoreRawSolutions], SolutionsSoFar, Solutions, IndicesOfDistinctionSoFar, IndicesOfDistinction) :-
  (
    findall(IndexOfDistinction, (select((_M2, Indices2), MoreRawSolutions, _Rest), once(distinct(Indices1, Indices2, [IndexOfDistinction]))), NewIndicesOfDistinction),
    % N solutions must have N-1 distinctions to be distinct
    length([(M1, Indices1)|MoreRawSolutions], NumberOfSolutions),
    NumberOfDistinctions is NumberOfSolutions-1,
    length(NewIndicesOfDistinction, NumberOfDistinctions)
    ->
    append(NewIndicesOfDistinction, IndicesOfDistinctionSoFar, NewIndicesOfDistinctionSoFar),
    solutions_are_pairwise_distinct(MoreRawSolutions, [(M1, Indices1)|SolutionsSoFar], Solutions, NewIndicesOfDistinctionSoFar, IndicesOfDistinction)
  ;
    % activate the commented line and deactivate the "fail" line to get partial results for the case that not all solutions are pairwise distinct
    % however, currently not all possible partial results are found
    %%% solutions_are_pairwise_distinct(MoreRawSolutions, SolutionsSoFar, Solutions, IndicesOfDistinctionSoFar, IndicesOfDistinction)
    fail
  ).


distinct(Indices1, Indices2, [IndexOfDistinction]) :-
  (
    % distinct noun phrases
    % case "There are two blue cows. There are three red cows. No blue cow is a red cow. |- There are how many cows?" 
    % case "John sees a man who Mary loves. John sees two men who Mary hates. No man who Mary loves is a man who Mary hates. |- John sees how many men?"
    % case "There are 2.1 l of cold water. There are 3.2 l of warm water. All cold water is not some warm water. |- There is how much water?"
    % case "There are 2.1 l of water that boils. There are 3.2 l of water that freezes. All water that boils is not some water that freezes. |- There is how much water?"    
    distinct_noun_phrases(Indices1, Indices2, [IndexOfDistinction])
    ->
    true
  ;
    % distinct derived noun phrases
    % case "Every man is a human. Every woman is a human. Mary is a woman. John is a man. |- There are how many humans?" 
    % case "Every man is a human. Every woman is a human. Mary is a woman. John is a man. |- There are 2 humans." 
    distinct_derived_noun_phrases(Indices1, Indices2, [IndexOfDistinction])
    ->
    true
  ;
   % distinct variables 
    % case "There are two cows X. There are three cows Y. X are not Y. |- There are how many cows?" 
    % case "There are two blue cows X. There are three red cows Y. There are 5 white cows Z. X are not Y. Y are not Z. X are not Z. |- There are how many cows?"
    % case "There are 2.1 l of water X. There are 3.2 l of water Y. X is not Y. |- There is how much water?"
    % case "There are 2.1 l of water X. All water is some fluid. There are 3.2 l of water Y. X is not Y. |- There is how much fluid?"
    % case "There is a man X. There is a man Y. X is not Y. Every man is a person. |- There are two persons."
    distinct_variables(Indices1, Indices2, [IndexOfDistinction])
    ->
    true
  ;
    % distinct predecessors
    % case "There are two lions. There are three tigers. No lion is a tiger. Every lion is a cat. Every tiger is a cat. |- There are how many cats?"
    % case "There are 2.1 l of water. All water is some fluid. There are 3.2 l of oil. All oil is some fluid. All water is not some oil. |- There is how much fluid?"
    % case "There are 2.1 l of water X. All water is some fluid. There are 3.2 l of water Y. X is not Y. |- There is how much fluid?"
    % case "There is a man X. There is a man Y. X is not Y. Every man is a person. |- There are two persons."
    distinct_predecessors(Indices1, Indices2, [IndexOfDistinction])
    ->
    true
  ;
    % distinct names
    % case "John is a man. Harry is a man. |- There are how many men?" (answer = 2)
    % distinct names but identical named objects
    % case "John is a man. Harry is a man. John is Harry. |- There are how many men?" (answer = 1)
    distinct_names(Indices1, Indices2, [IndexOfDistinction])
  ).
  /*
  %%% activate the following lines to get a trace of the axioms and theorems used for the proof Axioms |- Theorems
  %%%  also activate the respective lines 295 ... and 337 ... in satchmo/3
  user:axioms_theorems(Axioms, Theorems),
  (
    IndexOfDistinction = axiom(I),
    (
      I = 0
      ->
	  true
    ;
	  nth1(I, Axioms, Axiom),
	  nl, write('Axiom used in proof:   '), write(Axiom)
    )
  ;
    IndexOfDistinction = theorem(I),
    (
	  I = 0
	  ->
	  true
    ;
	  nth1(I, Theorems, Theorem),
	  nl, write('Theorem used in proof: '), write(Theorem)
    )
  ).
  */

distinct_noun_phrases(Indices1, Indices2, IndexOfDistinction) :-
  % there is an object/7 definition with Indices1
  exists_asserted_atom(object(World, _A1, Noun1, Class, Measure, _EQ1, _N1), Indices1),
  % there is an object/7 definition with Indices2
  exists_asserted_atom(object(World, _A2, Noun2, Class, Measure, _EQ2, _N2), Indices2),
  % the two object/7 definitions refer to distinct classes Noun1 and Noun2
  % i.e. there is a clause derived from "no (modified) Noun1 is a (modified) Noun2" or from "no (modified) Noun2 is a (modified) Noun1"
  user:clauses(Clauses), 
  member(satchmo_clause(Body, _Head, IndexOfDistinction), Clauses), \+ support:subterm(query(_, _, _), Body),
  eliminate_conjunct(Body, object(World, A12, Noun1, Class, _Measure, _EQ, _Num), Body1),
  eliminate_conjunct(Body1, object(World, A22, Noun2, Class, _Measure, _EQ, _Num), Body2), 
  (
    (eliminate_conjunct(Body2, predicate(World, _, be_NP, A12, A22), Body3) ; eliminate_conjunct(Body2, predicate(World, _, be_ADJ, A12, A22), Body3))
    ->
    true
  ; 
    (eliminate_conjunct(Body2, predicate(World, _, be_NP, A22, A12), Body3) ; eliminate_conjunct(Body2, predicate(World, _, be_ADJ, A22, A12), Body3))
  ),
  prove_RestBody(Body3, Indices1, Indices2).
  

distinct_derived_noun_phrases(Indices1, Indices2, IndexOfDistinction) :-
  % there is an object/7 definition for Noun with Indices1
  exists_asserted_atom(object(World, A1, Noun, Class, Measure, _EQ1, _N1), Indices1),
  % there is an object/7 definition for Noun with Indices2
  exists_asserted_atom(object(World, A2, Noun, Class, Measure, _EQ2, _N2), Indices2),
  eliminate_conjunct(Body, object(World, A12, Noun1, Class, _Measure, _EQ, _Num), Body1),
  eliminate_conjunct(Body1, object(World, A22, Noun2, Class, _Measure, _EQ, _Num), Body2), 
  (
    (eliminate_conjunct(Body2, predicate(World, _, be_NP, A12, A22), Body3) ; eliminate_conjunct(Body2, predicate(World, _, be_ADJ, A12, A22), Body3))
    ->
    true
  ; 
    (eliminate_conjunct(Body2, predicate(World, _, be_NP, A22, A12), Body3) ; eliminate_conjunct(Body2, predicate(World, _, be_ADJ, A22, A12), Body3))
  ),
  prove_RestBody(Body3, Indices1, Indices2).
 

prove_RestBody(true, _Indices1, _Indices2).

prove_RestBody(Conjunct, Indices1, Indices2) :-
  \+ Conjunct = (_, _),
  (exists_asserted_atom(Conjunct, Indices1) ; exists_asserted_atom(Conjunct, Indices2)).
  
prove_RestBody((Conjunct, Conjuncts), Indices1, Indices2) :-
  (exists_asserted_atom(Conjunct, Indices1) ; exists_asserted_atom(Conjunct, Indices2)),
  prove_RestBody(Conjuncts, Indices1, Indices2).


distinct_variables(Indices1, Indices2, IndexOfDistinction) :-
  % there is an object/7 definition for Noun with Indices1
  exists_asserted_atom(object(World, A1, Noun, Class, Measure, _EQ1, _N1), Indices1),
  % there is an object/7 definition for Noun with Indices2
  exists_asserted_atom(object(World, A2, Noun, Class, Measure, _EQ2, _N2), Indices2),
  % the two object/7 definitions have distinct referents
  % i.e. there is a clause derived from "no (Noun) X is (Noun) Y" or from "no (Noun) Y is (Noun) X"
  user:clauses(Clauses), 
  (
    member(satchmo_clause(predicate(World, _, be_NP, A1, A2), fail, IndexOfDistinction), Clauses)
  ;
    member(satchmo_clause(predicate(World, _, be_NP, A2, A1), fail, IndexOfDistinction), Clauses)
  ).


distinct_predecessors(Indices1, Indices2, IndexOfDistinction) :-
  % find distinct predecessors of the atoms with Indices1 and Indices2
  % there is an object/7 definition used to generate the atom with Indices1
  exists_asserted_atom(object(World, _A1, Noun1, Class, Measure, _EQ1, _N1), I1), 
  I1 \= Indices1, \+ intersection(Indices1, I1, []),
  % there is an object/7 definition used to generate the atom with Indices2
  exists_asserted_atom(object(World, _A2, Noun2, Class, Measure, _EQ2, _N2), I2), 
  I2 \= Indices2, \+ intersection(Indices2, I2, []),
  (
    % the two object/7 definitions refer to distinct classes Noun1 and Noun2
    % i.e. there is a clause derived from "no Noun1 is a Noun2" or from "no Noun2 is a Noun1"
    user:clauses(Clauses), 
    member(satchmo_clause(Body, _Head, IndexOfDistinction), Clauses), \+ support:subterm(query(_, _, _), Body),  
    support:subterm(object(World, A12, Noun1, Class, Measure1, EQ1, Num1), Body),
    support:subterm(object(World, A22, Noun2, Class, Measure1, EQ1, Num1), Body),
    (support:subterm(predicate(World, _, be_NP, A12, A22), Body) ; support:subterm(predicate(World, _, be_NP, A22, A12), Body))
    ->
    true
  ;
    % the two object/7 definitions have distinct referents
    % i.e. there is a clause derived from "no (Noun) X is (Noun) Y" or from "no (Noun) Y is (Noun) X"
    distinct_variables(I1, I2, IndexOfDistinction)
  ).


distinct_names(Indices1, Indices2, [axiom(0)]) :-
  % there is an object/7 definition for Noun with Indices1
  exists_asserted_atom(object(World, A1, Noun, Class, Measure, _EQ1, _N1), Indices1),
  % there is an object/7 definition for Noun with Indices2
  exists_asserted_atom(object(World, A2, Noun, Class, Measure, _EQ2, _N2), Indices2),
  % the two object/7 definitions are related by copulas to distinct names Name1 and Name2
  exists_asserted_atom(predicate(World, _, be_NP, N1, A1), Indices1),
  exists_asserted_atom(object(World, N1, Name1, named, na, eq, 1), [axiom(0)]),
  exists_asserted_atom(predicate(World, _, be_NP, N2, A2), Indices2),
  exists_asserted_atom(object(World, N2, Name2, named, na, eq, 1), [axiom(0)]),
  % names Name1 and Name2 are distinct
  Name1 \= Name2,
  % there are no statements "Name1 is Name2" or "Name2 is Name1" that would make the two named objects identical
  (
    (exists_asserted_atom(predicate(World, _, be_ID, N1, N2), Index) ; exists_asserted_atom(predicate(World, _, be_ID, N2, N1), Index))
    ->
    % Index is saved in identical_named_objects/3 to be used in satchmo:assimilate_closed_branch/1
    user:assert(identical_named_objects(Indices1, Indices2, Index)), 
    atomic_list_concat(['The names "', Name1, '" and  "', Name2, '" refer to the same object of the same class. Thus there will be less objects of this class than perhaps expected.'], MessageText),
    add_warning_message_once('aggregation', '', MessageText, ''),
    fail
  ;
    true
  ).


aggregate_solutions(Solutions, IndicesOfDistinction, TotalCount, Indices) :-
  aggregate_solutions(Solutions, 0, TotalCount, [], ListOfIndices),
  flatten(ListOfIndices, FlattenedListOfIndices),
  append([IndicesOfDistinction, FlattenedListOfIndices], AllIndices),
  list_to_set(AllIndices, Indices).

aggregate_solutions([], TotalCount, TotalCount, ListOfIndices, ListOfIndices).

aggregate_solutions([(M, Index) | Solutions], CountSoFar, N, ListOfIndicesSoFar, ListOfIndices) :-
  NewCount is CountSoFar + M,
  aggregate_solutions(Solutions, NewCount, N, [Index|ListOfIndicesSoFar], ListOfIndices).


%---------------------------------------------------------------------------------------------------------
%
%  pigeon holing
%
%---------------------------------------------------------------------------------------------------------
/*
% pigeon holing: more than one pigeon
prolog_axiom_text(pigeonholing1, 'Prolog Axiom pigeonholing1: more than one pigeon').
prolog_axiom(object(_World, _ReferentPigeon, Pigeon, countable, na, greater, 1), _IndicesSoFar, [prolog_axiom(pigeonholing1)|Indices]) :- 
  user:clauses(Clauses), 
  member(satchmo_clause((object(_, _, Pigeon, countable, na, greater, 1), object(_, _, Hole, countable, na, geq, 1), predicate(_, _, be, _), modifier_pp(_, _, Preposition, _)), fail, _), Clauses),
  pigeons_in_holes(Pigeon, Hole, Preposition, Indices).

% pigeon holing: at least one hole
prolog_axiom_text(pigeonholing2, 'Prolog Axiom pigeonholing2: at least one hole').
prolog_axiom(object(_World, _ReferentHole, Hole, countable, na, geq, 1), _IndicesSoFar, [prolog_axiom(pigeonholing2)|Indices]) :- 
  user:clauses(Clauses), 
  member(satchmo_clause((object(_, _, Pigeon, countable, na, greater, 1), object(_, _, Hole, countable, na, geq, 1), predicate(_, _, be, _), modifier_pp(_, _, Preposition, _)), fail, _), Clauses),
  pigeons_in_holes(Pigeon, Hole, Preposition, Indices).

% pigeon holing: pigeon in hole
prolog_axiom_text(pigeonholing3, 'Prolog Axiom pigeonholing3: pigeon in hole').
prolog_axiom(predicate(_World, _ReferentPredicate, be, _ReferentPigeon), _IndicesSoFar, [prolog_axiom(pigeonholing3)|Indices]) :- 
  user:clauses(Clauses), 
  member(satchmo_clause((object(_, _, Pigeon, countable, na, greater, 1), object(_, _, Hole, countable, na, geq, 1), predicate(_, _, be, _), modifier_pp(_, _, Preposition, _)), fail, _), Clauses),
  pigeons_in_holes(Pigeon, Hole, Preposition, Indices).

% pigeon holing: pigeon in hole
prolog_axiom_text(pigeonholing4, 'Prolog Axiom pigeonholing3: pigeon in hole').
prolog_axiom(modifier_pp(_World, _ReferentPredicate, Preposition, _ReferentHole), _IndicesSoFar, [prolog_axiom(pigeonholing3)|Indices]) :- 
  user:clauses(Clauses), 
  member(satchmo_clause((object(_, _, Pigeon, countable, na, greater, 1), object(_, _, Hole, countable, na, geq, 1), predicate(_, _, be, _), modifier_pp(_, _, Preposition, _)), fail, _), Clauses),
  pigeons_in_holes(Pigeon, Hole, Preposition, Indices).


pigeons_in_holes(Pigeon, Hole, Preposition, Indices) :-
  % "geq" part of "exactly NumberOfPigeons pigeons"
  exists_asserted_atom(object(World, ReferentPigeon, Pigeon, countable, na, geq, NumberOfPigeons), IndicesPigeon),
  % "geq" part of "exactly NumberOfHoles holes"
  exists_asserted_atom(object(World, ReferentHole, Hole, countable, na, geq, NumberOfHoles), IndicesHoles),
  NumberOfPigeons > NumberOfHoles,
  exists_asserted_atom(predicate(World, ReferentPredicate, be, ReferentPigeon), _IndicesBe),
  exists_asserted_atom(modifier_pp(World, ReferentPredicate, Preposition, ReferentHole), _IndicesPreposition),
  user:clauses(Clauses), 
  % "greater" part of "exactly NumberOfPigeons pigeons"
  member(satchmo_clause(object(World, RefPigeon2, Pigeon, countable, na, greater, NumberOfPigeons), fail, IndicesPigeon), Clauses), 
  % "greater" part of "exactly NumberOfHoles holes"
  member(satchmo_clause(object(World, RefHole2, Hole, countable, na, greater, NumberOfHoles), fail, IndicesHoles), Clauses), 
  % "geq" part of "every pigeon is in exactly one hole"
  member(satchmo_clause(object(World, RefPigeon3, Pigeon, countable, na, geq, 1), (object(World, RefHole3, Hole, countable, na, geq, 1), modifier_pp(World, RefBe1, Preposition, RefHole3), predicate(World, RefBe1, be, RefPigeon3)), IndicesPigeonInHole), Clauses),
  % "greater" part of "every pigeon is in exactly one hole"
  member(satchmo_clause((object(World, RefPigeon3, Pigeon, countable, na, geq, 1), object(World, RefHole4, Hole, countable, na, greater, 1), modifier_pp(World, RefBe2, Preposition, RefHole4), predicate(World, RefBe2, be, _G4206)), fail, IndicesPigeonInHole), Clauses),
  !,
  append([IndicesPigeon, IndicesHoles, IndicesPigeonInHole], RawIndices),
  list_to_set(RawIndices, Indices).
*/  


%---------------------------------------------------------------------------------------------------------
