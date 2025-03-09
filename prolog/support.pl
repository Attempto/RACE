%---------------------------------------------------------------------------------------------------------
%
%  Supporting Predicates
% 
%  N. E. Fuchs
%  University of Zurich
%
%  6 January 2016
%
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
%  declarations
%
%---------------------------------------------------------------------------------------------------------

% module definition and exported predicates
:- module(support, [
                    substitute/4,
                    subterm/2,
                    generate_subset/2,
                    subsets_in_size_order/2,
                    conjunction_to_list/2,
                    list_to_conjunction/2,
                    eliminate_conjunct/3,
                    variable_subtract/3,
                    variable_membercheck/2,
                    exists_asserted_atom/2
                   ]).

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
%  substitute(+Old, +New, +OldTerm, -NewTerm) 
%
%    unifies NewTerm with a copy of OldTerm in which all subterms identical to Old are replaced by New
%
%    (originally in Sterling & Shapiro, modified by O'Keefe)
%
%---------------------------------------------------------------------------------------------------------

substitute(Old, New, OldTerm, NewTerm) :-
  (
    OldTerm == Old 
    ->
    NewTerm = New
  ;   
    var(OldTerm) 
    ->
    NewTerm = OldTerm
  ;   
    functor(OldTerm, F, N),
    functor(NewTerm, F, N),
    substitute_args(Old, New, OldTerm, NewTerm, N)
  ).

substitute_args(Old, New, OldTerm, NewTerm, N) :-
  (   
    N =:= 0 
    ->
    true
  ;
    % N > 0 
    arg(N, OldTerm, OldArg),
    arg(N, NewTerm, NewArg),
    substitute(Old, New, OldArg, NewArg),
    M is N - 1,
    substitute_args(Old, New, OldTerm, NewTerm, M)
  ).

	
%---------------------------------------------------------------------------------------------------------
%
%  subterm(?Sub, +Term) 
%
%  	Sub is a subterm of Term
%   (source: J. Wielemaker, modified so that Term must always be instantiated)
%
%---------------------------------------------------------------------------------------------------------

subterm(Sub, Term) :-
  nonvar(Term),
  Sub = Term.

subterm(Sub, Term) :-
  compound(Term),
  arg(_, Term, Arg),
  subterm(Sub, Arg).
 

%---------------------------------------------------------------------------------------------------------
%
%  generate_subset(+Set, ?SubSet) 
%    SubSet is a subset of Set
%
%  subsets_in_size_order(+Set, ?SubSet)
%    SubSet is a subset of Set where subsets are generated in increasing length
%
%---------------------------------------------------------------------------------------------------------

generate_subset([], []).

generate_subset([X|Xs], [X|Ys]):-
  generate_subset(Xs, Ys).
  
generate_subset([_X|Xs], Ys):-
  generate_subset(Xs, Ys).
    
    
subsets_in_size_order(Set, Sub) :-
  length(Set, N),
  between(0, N, L),
  length(Sub, L),
  generate_subset(Set, Sub).
  
	
%---------------------------------------------------------------------------------------------------------
%
%  conjunction_to_list(+Conjunction, -List)
%
%    convert Conjunction into List
%    restriction: Conjunction is not empty (true)
% 
%
%  list_to_conjunction(+List, -Conjunction)
%
%    convert List into Conjunction
%    restriction: List is not empty ([])
%
%---------------------------------------------------------------------------------------------------------

conjunction_to_list((A,B), [A|List]) :-
  !,
  conjunction_to_list(B, List).

conjunction_to_list(A, [A]).


list_to_conjunction([A|List], (A,B)) :-
  List \= [],
  !,
  list_to_conjunction(List, B).

list_to_conjunction([A], A).


%---------------------------------------------------------------------------------------------------------
%
%  eliminate_conjunct(+Conjunction, +Conjunct, -NewConjunction)
%
%    NewConjunction is Conjunction without Conjunct
%    if Conjunction is just one conjunct and Conjunction = Conjunct then NewConjunction = true
%
%---------------------------------------------------------------------------------------------------------

% return "true" if Conjunction consists of only one element matching Conjunct
eliminate_conjunct(Conjunction, Conjunct, NewConjunction) :-
  Conjunction \= (_, _),
  Conjunct = Conjunction
  ->
  NewConjunction = true.

eliminate_conjunct((Conjunct1, MoreConjuncts), Conjunct, NewConjunction) :-
  (
    Conjunct1 = Conjunct, 
    NewConjunction = MoreConjuncts
  ;
    eliminate_conjunct(MoreConjuncts, Conjunct, IntermediateConjunction),
    NewConjunction = (Conjunct1, IntermediateConjunction)
  ).


%---------------------------------------------------------------------------------------------------------
%
%  variable_subtract(+Variables1, +Variables2, -Variables3)
%
%  list Variables3 contains those variables of list Variables1 that do not occur in list Variables2
%
%---------------------------------------------------------------------------------------------------------

variable_subtract([], _, []).

variable_subtract([Element|Elements], Set, Difference) :-
  variable_membercheck(Element, Set),
  !,
  variable_subtract(Elements, Set, Difference).

variable_subtract([Element|Elements], Set, [Element|Difference]) :-
  variable_subtract(Elements, Set, Difference).


variable_membercheck(X, [E|_]) :- 
  E==X,
  !.

variable_membercheck(X, [_|L]) :- 
  variable_membercheck(X, L).
  
  
%---------------------------------------------------------------------------------------------------------
%
%  exists_asserted_atom(+Atom, ?Index)
%
%---------------------------------------------------------------------------------------------------------

exists_asserted_atom(Atom, Index) :-
  user:Atom,
  term_hash(Atom, HashOfAtom),
  user:indices(HashOfAtom, Index).


%---------------------------------------------------------------------------------------------------------