%---------------------------------------------------------------------------------------------------------
%
%  RACE Interfaces
%
%  Procedure calls for RACE
% 
%  N. E. Fuchs
%  University of Zurich
%
%  26 March 2024
%
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
%  declarations
%
%---------------------------------------------------------------------------------------------------------

% module definition and exported predicates
:- module(race, [check_consistency/5, 
                 prove/7, 
                 answer_query/7]).

% compilation settings
%:- check.
:- style_check([-discontiguous]).
%%%%%%:- set_prolog_flag(compile_meta_arguments, control). % enabling makes tracing hard to follow

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

% library modules
:- use_module(library(debug)).
:- use_module(library(lists)).
:- use_module(library(time)).  
:- use_module(library(clpr)).  
:- use_module(library(ansi_term)). % needed to colour the SWI compiler output

% RACE modules
:- use_module(ape_client).
:- use_module(drs_to_fol).
:- use_module(transform_fol_axioms).
:- use_module(fol_to_clauses).
:- use_module(satchmo).
:- use_module(support).
:- use_module(auxiliary_axioms).
:- use_module(race_error_logger).

% APE modules
:- use_module('../ape/parser/ace_to_drs').
:- use_module('../ape/parser/ape_utils').
:- use_module('../ape/parser/tokenizer').
:- use_module('../ape/utils/morphgen', [acesentencelist_pp/2]).
:- use_module('../ape/utils/drs_to_drslist').
:- use_module('../ape/utils/ace_niceace').
:- use_module('../ape/utils/is_wellformed', [is_wellformed/1]).
:- use_module('../ape/utils/drs_to_ascii').
:- use_module('../ape/utils/trees_to_ascii').
:- use_module('../ape/utils/drs_to_ace', [drs_to_ace/2]).
%:- use_module('../ape/logger/error_logger').

% lexicon modules
:- style_check(-singleton).
:- use_module('../ape/lexicon/clex').
:- use_module('../ape/lexicon/ulex').
:- style_check(+singleton).

% global dynamic predicates
:- user:dynamic(clauses/1).
:- user:dynamic(indices/2).
:- user:dynamic(object/7).
:- user:dynamic(property/4).
:- user:dynamic(property/5).
:- user:dynamic(property/7).
:- user:dynamic(relation/5).
:- user:dynamic(predicate/4).
:- user:dynamic(predicate/5).
:- user:dynamic(predicate/6).
:- user:dynamic(modifier_adv/4).
:- user:dynamic(modifier_pp/4).
:- user:dynamic(has_part/3).
:- user:dynamic(formula/4).
:- user:dynamic(query/3).
:- user:dynamic(accessibility_relation/2).
:- user:dynamic(identical_named_objects/3).


%---------------------------------------------------------------------------------------------------------
%
%  parameter for all three interfaces
%
%    raw   show all raw proofs together with auxiliary axioms
%
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
%  check_consistency(+Axioms, +Parameters, -Messages, -RunTime, -Proofs)
%
%  check_consistency(+Axioms, +Parameters, -Messages, -Proofs)
%
%  check_consistency_DRS(+AxiomsDRS, +AxiomsText, -Messages, -Proofs) 
%
%  Check the consistency of Axioms – consisting of a mixture of any ACE sentence type – using the     
%  settings Parameters. Messages contains any error or warning messages generated. RunTime is the   
%  runtime of the proof. Proofs contains inconsistent subsets of Axioms, or is empty. The entry-point    
%  check_consistency_DRS/4 checks the consistency of the DRS AxiomsDRS derived from Axioms. 
%  AxiomsText is a list of list of tokens of the sentences of the Axioms.
%
%
%  parameter		value				description		
%  ---------		-----				-----------
%  Axioms 			string				axioms: ACE text
%  AxiomsDRS 		Prolog structure	axioms: DRS
%  AxiomsText 		list				axioms: list of list of tokens
%  Parameters		list				set of enabled parameters: see above
%  Messages			list of messages	error and warning messages
%  RunTime			integer				RACE runtime in ms
%  Proofs			list of terms		results of check: subsets of inconsistent ACE axioms and auxiliary 
%					proof/2 where the   axioms; empty if Axioms are consistent
%                   first argument is
%                   a list of ACE axioms,
%                   the second argument a
%                   list of auxiliary axioms
%
%---------------------------------------------------------------------------------------------------------

check_consistency(Axioms, Parameters, Messages, RunTime, Proofs) :-
  time(check_consistency(Axioms, Parameters, Messages, Proofs), RunTime).

check_consistency(Axioms, Parameters, Messages, Proofs) :-
  % clean-up from previous run
  clean_up,
  % set global parameters plus indicator that we are in check_consistency
  nb_setval(global_parameters, [check_consistency|Parameters]),
  % translate Axioms into DRS
  acetext_to_drs(Axioms, drs(RsA,CsA), TextA, MessagesAPE),
  (
    % Axioms cannot be parsed
    \+ MessagesAPE = [], 
    memberchk(message(error, _, _, _, _), MessagesAPE)
    ->
    Messages = [message(error, race, ''-'', 'Axioms cannot be parsed.', 'Correct the axioms.')|MessagesAPE],
    Proofs = []
  ;
    % Axioms can be parsed
    catch(call(check_consistency_DRS(drs(RsA,CsA), TextA, Messages, Proofs)), CatchType, 
      (
        race_error_logger:get_messages(RACEMessages), 
        (
          % there are no specific RACE messages thus there is an internal error
          RACEMessages = []
          -> 
          term_to_atom(CatchType, CatchTypeAsAtom),
          atomic_list_concat(['Internal error: ', CatchTypeAsAtom], MessageText),
          Messages = [message(error, race, ''-'', MessageText, 'Contact RACE developers.')]
        ;
         % there are specific RACE messages
         Messages = RACEMessages
        ),
        Proofs = []
      )
    )
  ).  
      
check_consistency_DRS(drs(RsA,CsA), TextA, Messages, Proofs) :-    
  % assert ACE axioms and empty ACE theorems for trace of proof
  user:assert(axioms_theorems(TextA, [])),
  % transform DRSs into FOL
  drs_to_fol(drs(RsA,CsA), axiom, World, FormulaAxioms), 
  % clausify Axioms and - if they exist - FOL axioms
  (
    % conjoin all FOL axioms into one formula
	% transform_fol_axioms/1 fails if there are no FOL axioms
	transform_fol_axioms(World, FormulaFOLAxioms)
	->
	% use new variables for the FOL axioms
	copy_term(FormulaFOLAxioms, CopiedFormulaFOLAxioms),
	% clausify conjunction of Axioms and FOL axioms with World argument existentially quantified
	fol_to_clauses(exists(World, FormulaAxioms & CopiedFormulaFOLAxioms), Clauses)
  ;
	% transform_fol_axioms/1 failed
	% clausify Axioms
	fol_to_clauses(exists(World, FormulaAxioms), Clauses)
  ),
  !, 
  % run satchmo 
  satchmo(Clauses, _Models, Inconsistencies),
  % before activating the following line change in the preceding line _Models into Models
  %%%nl, write('Models: '), write(Models),
  %%%nl, write('Inconsistencies: '), write(Inconsistencies),
  % check for Satchmo error messages
  get_messages(Messages),
  (
	% there are no error messages
	\+ member(message(error, race, _, _, _), Messages)
	->
	(
	  % Axioms are inconsistent
	  Inconsistencies = [_|_]
	  ->
	  collect_all_proofs(Inconsistencies, TextA, Proofs)
	;
	  % Axioms are consistent
	  Proofs = []
	)
  ;
	% if there are error messages then suppress proofs
	Proofs = []
  ).


%---------------------------------------------------------------------------------------------------------
%
%  prove(+Axioms, +Theorems, +Parameters, -Messages, -RunTime, -Proofs, -WhyNot)
%
%  prove(+Axioms, +Theorems, +Parameters, -Messages, -Proofs, -WhyNot)
%
%  prove_DRS(+AxiomsDRS, +AxiomsText, +TheoremsDRS, +TheoremsText, -Messages, -Proofs, -WhyNot) 
%
%  Prove purely declarative ACE Theorems from purely declarative ACE Axioms using the settings Parameters. 
%  Messages contains any error or warning messages generated. RunTime is the runtime of the proof. Proofs  
%  contains subsets of Axioms that allow to prove Theorems, or is empty if there is no proof. WhyNot contains 
%  words of Theorems that could not be proved, or is empty if the proof succeeds.
%
%  The entry-point proof_DRS/7 proves the DRS TheoremsDRS – derived from ACE theorems – from the 
%  DRS AxiomsDRS – derived from ACE axioms. AxiomsText/TheoremsText is a list of list of tokens of the 
%  sentences of the ACE axioms/theorems.
%
%  parameter		value				description		
%  ---------		-----				-----------
%  Axioms 			string				axioms: ACE text
%  AxiomsDRS 		Prolog structure	axioms: DRS
%  AxiomsText 		list				axioms: list of list of tokens
%  Theorems 		string				theorems: ACE text
%  TheoremsDRS 		Prolog structure	theorems: DRS
%  TheoremsText 	list				theorems: list of list of tokens
%  Parameters		list				set of enabled parameters: see above
%  Messages			list of messages	error and warning messages
%  RunTime			integer				RACE runtime in ms
%  Proofs			list of terms		results of proof: subsets of Axioms and auxiliary axioms used to
%					proof/2 where the   prove Theorems; empty if proof fails
%                   first argument is
%                   a list of ACE axioms,
%                   the second argument a
%                   list of auxiliary axioms
%  WhyNot			list of words		if proof fails: list of words and language constructs of   
%                                       Theorem that could not be proved; empty if proof succeeds
%
%---------------------------------------------------------------------------------------------------------

prove(Axioms, Theorems, Parameters, Messages, RunTime, Proofs, WhyNot) :-
  time(prove(Axioms, Theorems, Parameters, Messages, Proofs, WhyNot), RunTime).

prove(Axioms, Theorems, Parameters, Messages, Proofs, WhyNot) :-
  % clean-up from previous run
  clean_up,
  % set global parameters plus indicator that we are in prove
  nb_setval(global_parameters, [prove|Parameters]),
  % translate Axioms into DRS
  acetext_to_drs(Axioms, drs(RsA,CsA), TextA, MessagesAPEA),
  (
	% Axioms cannot be parsed
	\+ MessagesAPEA = [], 
	memberchk(message(error, _, _, _, _), MessagesAPEA)
	->
	Messages = [message(error, race, ''-'', 'Axioms cannot be parsed.', 'Correct axioms.')|MessagesAPEA],
	Proofs = [],
	WhyNot = []
  ;
    % Axioms can be parsed but contain questions and/or commands
    (memberchk(question(_), CsA) ; memberchk(command(_), CsA))
    ->
    Messages = [message(error, race, ''-'', 'Axioms contain questions and/or commands.', 'Submit purely declarative axioms.')|MessagesAPEA],
    Proofs = [],
	WhyNot = []
  ;
	% Axioms can be parsed and are purely declarative
	% translate Theorems into DRS
	acetext_to_drs(Theorems, drs(RsT,CsT), TextT, MessagesAPET),
    (
	  % Theorems cannot be parsed
	  \+ MessagesAPET = [], 
	  memberchk(message(error, _, _, _, _), MessagesAPET)
	  ->
	  Messages = [message(error, race, ''-'', 'Theorems cannot be parsed.', 'Correct the theorems.')|MessagesAPET],
	  Proofs = [],
      WhyNot = []
    ;
      % Theorems can be parsed but contain questions and/or commands
      (memberchk(question(_), CsT) ; memberchk(command(_), CsT))
      ->
      Messages = [message(error, race, ''-'', 'Theorems contain questions and/or commands.', 'Submit purely declarative theorems.')|MessagesAPET],
      Proofs = [],
      WhyNot = []
	;
	  % Axioms and Theorems can be parsed
	  % prove Theorems from Axioms
      catch(call(prove_DRS(drs(RsA,CsA), TextA, drs(RsT,CsT), TextT, Messages, Proofs, WhyNot)), CatchType, 
        (
          race_error_logger:get_messages(RACEMessages), 
          (
            % there are no specific RACE messages thus there is an internal error
            RACEMessages = []
            -> 
            term_to_atom(CatchType, CatchTypeAsAtom),
            atomic_list_concat(['Internal error: ', CatchTypeAsAtom], MessageText),
            Messages = [message(error, race, ''-'', MessageText, 'Contact RACE developers.')]
          ;
           % there are specific RACE messages
           Messages = RACEMessages
          ),
          Proofs = [],
          WhyNot = []
        )
      )
    )
  ).

prove_DRS(drs(RsA,CsA), TextA, drs(RsT,CsT), TextT, Messages, Proofs, WhyNot) :-
  % assert ACE axioms and ACE theorems for trace of proof
  user:assert(axioms_theorems(TextA, TextT)),
  % transform DRSs into FOL using new variables for theorems
  drs_to_fol(drs(RsA,CsA), axiom, World, FormulaAxioms), 
  copy_term(drs(RsT,CsT), drs(CopiedRsT,CopiedCsT)),
  drs_to_fol(drs(CopiedRsT,CopiedCsT), theorem, World, FormulaTheorems),
  % clausify Axioms, negated Theorems and - if they exist - FOL axioms
  (
    % conjoin all FOL axioms into one formula
    % transform_fol_axioms/1 fails if there are no FOL axioms
    transform_fol_axioms(World, FormulaFOLAxioms)
    ->
    % use new variables for the FOL axioms
    copy_term(FormulaFOLAxioms, CopiedFormulaFOLAxioms),
    % clausify conjunction of Axioms, negated Theorems and FOL axioms with World argument existentially quantified
    fol_to_clauses(exists(World, FormulaAxioms & -FormulaTheorems & CopiedFormulaFOLAxioms), Clauses)
  ;
    % transform_fol_axioms/1 failed
    % clausify conjunction of Axioms and negated Theorems
    fol_to_clauses(exists(World, FormulaAxioms & -FormulaTheorems), Clauses)
  ),
  !, 
  % run satchmo 
  satchmo(Clauses, Models, Inconsistencies),
  %%%nl, write('Models: '), write(Models),
  %%%nl, write('Inconsistencies: '), write(Inconsistencies),
  % check for Satchmo error messages
  get_messages(SatchmoMessages),
  (
    % there are no error messages
    \+ member(message(error, race, _, _, _), SatchmoMessages)
    ->
    (
      % conjunction of Axioms and negated Theorems is inconsistent
      Inconsistencies = [_|_]
      ->
      % axioms could be inconsistent 
      (
        % axioms are consistent if all final inconsistencies contain a reference to the theorems
        % note: satchmo/collect_indices_of_all_inconsistent_clauses/1 can leave conditions disjunct/1 in final inconsistencies
        % note: axioms could also seem to be inconsistent due to the presence of a prolog_axiom 
        forall(member(Inconsistency, Inconsistencies), (member(theorem(_), Inconsistency) ; member(disjunct(_), Inconsistency); member(prolog_axiom(_), Inconsistency)))
        ->
        Messages = SatchmoMessages,
        collect_all_proofs(Inconsistencies, TextA, Proofs),
        WhyNot = []
      ;
        % axioms are inconsistent if a final inconsistency contains only references to axioms
        % exclude arithmetical problems that are caught in satchmo/3
        \+ member(message(error, race, ''-'', 'Arithmetic axioms are inconsistent or could not be evaluated.', 'Check arithmetic axioms.'), SatchmoMessages)
        ->
        Messages = [message(error, race, ''-'', 'Axioms are inconsistent. Any theorem can be derived.', 'Check axioms.')|SatchmoMessages],
        Proofs = [],
        WhyNot = []
      ;
        % member(message(error, race, ''-'', 'Arithmetic axioms are inconsistent or could not be evaluated.', 'Check arithmetic axioms.'), SatchmoMessages)
        Messages = SatchmoMessages,
        Proofs = [],
        WhyNot = []
      )
    ;
      % conjunction of Axioms and negated Theorems is consistent ...
      % Inconsistencies = []
      % ... yet Theorems could be inconsistent
      check_consistency_DRS(drs(RsT,CsT), TextT, _MessagesT, ProofsT),
      (
        % Theorems are inconsistent
        ProofsT \= []
        ->
        Messages = [message(error, race, ''-'', 'Theorems are inconsistent.', 'Check theorems.')|SatchmoMessages]
      ;
        % Theorems are consistent
        % ProofsT = []
        Messages = SatchmoMessages,
        Proofs = [],
        % Why could Theorems not be proved?
        why_not(Clauses, Models, WhyNot)
      )
 ) 
  ;
    % if there are error messages then suppress proofs and why not information
    Messages = SatchmoMessages,
    Proofs = [],
    WhyNot = []
  ).
  

%---------------------------------------------------------------------------------------------------------
%
%  answer_query(+Axioms, +Query, +Parameters, -Messages, -RunTime, -Proofs, -WhyNot)
%  synonym: answer_question(+Axioms, +Query, +Parameters, -Messages, -RunTime, -Proofs, -WhyNot)
%
%  answer_query(+Axioms, +Query, +Parameters, -Messages, -Proofs, -WhyNot)
%
%  answer_query_DRS(+AxiomsDRS, +AxiomsText, +QueryDRS, +QueryText, -Messages, -Proofs, -WhyNot) 
%
%  Answer ACE Query – consisting of one or more questions – from purely declarative ACE Axioms using the 
%  settings Parameters. Messages contains any error or warning messages generated. RunTime is the runtime 
%  of the proof. Proofs contains subsets of Axioms that allow to answer Query, or is empty if there is no 
%  answer. WhyNot contains words of Query that could not be proved, or is empty if there is an answer.
%
%  The entry-point answer_query__DRS/7 answers the DRS QueryDRS – derived from an ACE query – from 
%  the DRS AxiomsDRS – derived from ACE axioms. AxiomsText/QueryText is a list of list of tokens of the 
%  sentences of the ACE axioms/query.
%
%  RESTRICTION: yes/no queries; "who", "what" and "which" queries; "how", "when" and "where" queries are 
%  answered as "how" queries
%
%  parameter		value				description		
%  ---------		-----				-----------
%  Axioms 			string				axioms: ACE text
%  AxiomsDRS 		Prolog structure	axioms: DRS
%  AxiomsText 		list				axioms: list of list of tokens
%  Query  	 		string				query: ACE text
%  QueryDRS 		Prolog structure	query: DRS
%  QueryText 		list				query: list of list of tokens
%  Parameters		list				set of enabled parameters: see above
%  Messages			list of messages	error and warning messages
%  RunTime			integer				RACE runtime in ms
%  Proofs			list of terms		results of proof: subsets of Axioms and auxiliary axioms used to
%					proof/2 where the   answer Query, substitutions of query words; empty if there is no answer
%                   first argument is
%                   a list of ACE axioms and
%                   substitions of query words,
%                   the second argument a
%                   list of auxiliary axioms
%  WhyNot			list of words		if there is no answer: list of words and language constructs of   
%                                       Query that could not be proved; empty if there is an answer
%
%---------------------------------------------------------------------------------------------------------

% synonym for answer_query/7
answer_question(Axioms, Query, Parameters, Messages, RunTime, Proofs, WhyNot) :-
  answer_query(Axioms, Query, Parameters, Messages, RunTime, Proofs, WhyNot).

answer_query(Axioms, Query, Parameters, Messages, RunTime, Proofs, WhyNot) :-
  time(answer_query(Axioms, Query, Parameters, Messages, Proofs, WhyNot), RunTime).

answer_query(Axioms, Query, Parameters, Messages, Proofs, WhyNot) :-
  % clean-up from previous run
  clean_up,
  % set global parameters plus indicator that we are in answer_query
  nb_setval(global_parameters, [answer_query|Parameters]),
  % translate Axioms into DRS
  acetext_to_drs(Axioms, drs(RsA,CsA), TextA, MessagesAPEA),
  (
	% Axioms cannot be parsed
	\+ MessagesAPEA = [], 
	memberchk(message(error, _, _, _, _), MessagesAPEA)
	->
	Messages = [message(error, race, ''-'', 'Axioms cannot be parsed.', 'Correct the axioms.')|MessagesAPEA],
	Proofs = [],
	WhyNot = []
  ;
    % Axioms can be parsed but contain questions and/or commands
    (memberchk(question(_), CsA) ; memberchk(command(_), CsA))
    ->
    Messages = [message(error, race, ''-'', 'Axioms contain questions and/or commands.', 'Submit purely declarative axioms.')|MessagesAPEA],
    Proofs = [],
	WhyNot = []
  ;
	% Axioms can be parsed and are purely declarative
	% translate Query into DRS
	acetext_to_drs(Query, drs(RsQ,CsQ), TextQ, MessagesAPEQ),
	(
	  % Query cannot be parsed
	  \+ MessagesAPEQ = [], 
	  memberchk(message(error, _, _, _, _), MessagesAPEQ)
	  ->
	  Messages = [message(error, race, ''-'', 'Query cannot be parsed.', 'Correct the query.')|MessagesAPEQ],
	  Proofs = [],
	  WhyNot = []
	;
	  % Query can be parsed
      %%%%%% next line prevents facts occurring in the query
      RsQ = [],
      %%%%%%
      % query can contain exactly one or several questions
      % note 1: several identical query words – Who sees who? – already make the assignment of substitutions
      % to their respective query words difficult; allowing for several questions can effectively lead to confusion
      % note 2: several questions actually constitute several proofs
      % note 3: several questions make sense when solving linear equations whose results should best be reported at the same time
      %%%%%% to allow for more than one question: deactivate next line and replace it by "true"
      % CsQ = [question(drs(_Referents, _Conditions))] 
      true 
      %%%%%%
      ->
	  % prove Query from Axioms
      catch(call(answer_query_DRS(drs(RsA,CsA), TextA, drs(RsQ,CsQ), TextQ, Messages, Proofs, WhyNot)), CatchType, 
        (
          race_error_logger:get_messages(RACEMessages), 
          (
            % there are no specific RACE messages thus there is an internal error
            RACEMessages = []
            -> 
            term_to_atom(CatchType, CatchTypeAsAtom),
            atomic_list_concat(['Internal error: ', CatchTypeAsAtom], MessageText),
            Messages = [message(error, race, ''-'', MessageText, 'Contact RACE developers.')]
          ;
           % there are specific RACE messages
           Messages = RACEMessages
          ),
          Proofs = [],
          WhyNot = []
        )
      )
    ;
      % Query violates allowed form
      % check code above to see which form queries can have
      Messages = [message(error, race, ''-'', 'Query is not a single question, or contains facts.', 'Check query.')|MessagesAPEQ],
      Proofs = [],
      WhyNot = []
	)
  ).

answer_query_DRS(drs(RsA,CsA), TextA, drs(RsQ,CsQ), TextQ, Messages, Proofs, WhyNot) :-
  % assert ACE axioms and ACE queries for trace of proof
  user:assert(axioms_theorems(TextA, TextQ)),
  % transform DRSs into FOL using new variables for theorems
  drs_to_fol(drs(RsA,CsA), axiom, World, FormulaAxioms), 
  copy_term(drs(RsQ,CsQ), drs(CopiedRsQ,CopiedCsQ)),
  drs_to_fol(drs(CopiedRsQ, CopiedCsQ), theorem, World, FormulaQuery),
  % clausify Axioms, negated Query and - if they exist - FOL axioms
  (
    % conjoin all FOL axioms into one formula
    % transform_fol_axioms/1 fails if there are no FOL axioms
    transform_fol_axioms(World, FormulaFOLAxioms)
    ->
    % use new variables for the FOL axioms
    copy_term(FormulaFOLAxioms, CopiedFormulaFOLAxioms),
    % clausify conjunction of Axioms, negated Query and FOL axioms with World argument existentially quantified
    fol_to_clauses(exists(World, FormulaAxioms & -FormulaQuery & CopiedFormulaFOLAxioms), Clauses)
  ;
    % transform_fol_axioms/1 failed
    % clausify conjunction of Axioms and negated Query
    fol_to_clauses(exists(World, FormulaAxioms & -FormulaQuery), Clauses)
  ),
  !, 
  % run satchmo 
  satchmo(Clauses, Models, Inconsistencies),
  %%%nl, write('Models: '), write(Models),
  %%%nl, write('Inconsistencies: '), write(Inconsistencies),
  % check for Satchmo error messages
  get_messages(SatchmoMessages), 
  (
    % there are no error messages
    \+ member(message(error, race, _, _, _), SatchmoMessages)
    ->
    (
  	  % conjunction of Axioms and negated Query is inconsistent
  	  Inconsistencies = [_|_]
	  ->
      % axioms could be inconsistent 
      (
        % axioms are consistent if all final inconsistencies contain a reference to the theorems
        % note: satchmo/collect_indices_of_all_inconsistent_clauses/1 can leave conditions disjunct/1 in final inconsistencies 
        % note: axioms could also seem to be inconsistent due to the presence of a prolog_axiom 
        forall(member(Inconsistency, Inconsistencies), (member(theorem(_), Inconsistency) ; member(disjunct(_), Inconsistency); member(prolog_axiom(_), Inconsistency)))
        ->
        Messages = SatchmoMessages,
        collect_all_proofs(Inconsistencies, TextA, Proofs),
        WhyNot = []
      ;
        % axioms are inconsistent if a final inconsistency contains only references to axioms
        % exclude arithmetical problems that are caught in satchmo/3
        \+ member(message(error, race, ''-'', 'Arithmetic axioms are inconsistent or could not be evaluated.', 'Check axioms.'), SatchmoMessages)
        ->
        Messages = [message(error, race, ''-'', 'Axioms are inconsistent. Any answer can be derived.', 'Check axioms.')|SatchmoMessages],
        Proofs = [],
        WhyNot = []
      ;
        % member(message(error, race, ''-'', 'Arithmetic axioms are inconsistent or could not be evaluated.', 'Check axioms.'), SatchmoMessages)
        Messages = SatchmoMessages,
        Proofs = [],
        WhyNot = []
      )
    ;
	  % conjunction of Axioms and negated Query is consistent
	  % Inconsistencies = []
	  Messages = SatchmoMessages,
	  Proofs = [],
	  % Why could Query not be answered?
	  why_not(Clauses, Models, WhyNot)
    )
  ;
    % if there are error messages then suppress proofs and why not information
    Messages = SatchmoMessages,
    Proofs = [],
    WhyNot = []
  ).


%---------------------------------------------------------------------------------------------------------
%
%  join_sequence_of_questions_to_one_query(+SequenceOfQuestions, -Query)
%
%  Query is a DRS whose referents/conditions are a concatenation of the referents/conditions of a list
%  SequenceOfQuestions of query DRSs
%
%  join_sequence_of_questions_to_one_query fails if SequenceOfQuestions does not consist of query DRSs
%
%---------------------------------------------------------------------------------------------------------

join_sequence_of_questions_to_one_query(SequenceOfQuestions, Query) :-
  join_sequence_of_questions_to_one_query(SequenceOfQuestions, [], [], Query).

join_sequence_of_questions_to_one_query([], ListOfListOfReferents, ListOfListOfConditions, drs(ListOfReferents, ListOfConditions)) :-
  append(ListOfListOfReferents, ListOfReferents),
  append(ListOfListOfConditions, ListOfConditions).

join_sequence_of_questions_to_one_query(SequenceOfQuestions, ReferentsSoFar, ConditionsSoFar, Query) :-
   SequenceOfQuestions = [question(drs(Referents, Conditions))|MoreQuestions]
   ->
   join_sequence_of_questions_to_one_query(MoreQuestions, [Referents|ReferentsSoFar], [Conditions|ConditionsSoFar], Query).


%---------------------------------------------------------------------------------------------------------
%
%  collect_all_proofs(+Inconsistencies, +AllACEAxioms, -Proofs)
%
%  Inconsistencies is a list of lists containing the indices of ACE axioms, auxiliary FOL and Prolog  
%  axioms, and theorems used for each proof of the theorems from the axioms
%
%  AllACEAxioms is the set of all ACE axioms
%
%  Proofs is a list of terms proof(ACEAxioms, AuxiliaryAxioms) where each term stands for one proof;
%  ACEAxioms is a list of the ACE axioms used for the proof, while AuxiliaryAxioms is a list of the
%  auxiliary FOL and Prolog axioms used for the proof
%
%  if the parameter raw is set then Proofs shows all raw proofs together with the auxiliary axioms
%
%  if the parameter raw is not set then Proof shows only the proofs with the minimal sets ACEAxioms
%  and the lists AuxiliaryAxioms are empty
%
%---------------------------------------------------------------------------------------------------------

collect_all_proofs(Inconsistencies, AllACEAxioms, Proofs) :-
  remove_spurious_inconsistencies(Inconsistencies, RestInconsistencies),
  % find raw proofs
  findall(RawProof, (member(Indices, RestInconsistencies), convert_indices_to_sentences(Indices, AllACEAxioms, RawProof)), RawProofs),
  % if there are only proofs involving auxiliary axioms then activate "show raw proofs" for a minimum of results
  (
    forall(memberchk(Proof, RawProofs), Proof=proof([], [_|_]))
    ->
    nb_getval(global_parameters, CurrentParameters),
    nb_setval(global_parameters, [raw|CurrentParameters])
  ;
    true
  ),
  (
    % parameter "show all raw proofs (raw)" set
    % show complete proof results, i.e. minimal proofs, non-minimal proofs and auxiliary axioms
    nb_getval(global_parameters, Parameters),
    memberchk(raw, Parameters)
    ->
    sort(RawProofs, Proofs)
  ;
    % parameter "show all raw proofs (raw)" not set
    % eliminate proofs with empty list of axioms, i.e. proofs by auxiliary axioms alone or
    % completely empty proofs that could be generated by tautological theorems like 'A or not A'
    delete(RawProofs, proof([], _AuxiliaryAxioms), NonEmptyProofs),
    % eliminate non-minimal proofs & auxiliary axioms
    eliminate_non_minimal_proofs(NonEmptyProofs, MinimalProofs),
    % eliminate duplicates
    list_to_set(MinimalProofs, Proofs)
  ).


remove_spurious_inconsistencies(Inconsistencies, RestInconsistencies) :-
   (
    % remove spurious inconsistencies that can arise when a disjunct occurs in an axiom and ...
    % ... query elements or indefinite pronouns occur in a theorem
    % proofs succeed falsely for both branches of the disjunct
    % example: 'There is a man or there is a woman. There is no woman.'|- 'What is there?'
    % example: 'There is a man or there is a woman.' |- 'There is somebody.'
    % elimination is based on two criteria
    % first criterium: there is more than one occurrence of a query element or of an indefinite pronoun ...
    % ... referring to different objects
    member(Inconsistency, Inconsistencies),
    (
      member(what(_, _, Object1, _), Inconsistency), member(what(_, _, Object2, _), Inconsistency)
    ;
      member(what(Object1), Inconsistency), member(what(Object2), Inconsistency)
    ;
      member(who(_, _, Object1, _), Inconsistency), member(who(_, _, Object2, _), Inconsistency)
    ;
      member(who(Object1), Inconsistency), member(who(Object2), Inconsistency)
    ;
      member(somebody(_, _, Object1, _), Inconsistency), member(somebody(_, _, Object2, _), Inconsistency)
    ;
      member(somebody(Object1), Inconsistency), member(somebody(Object2), Inconsistency)
    ;
      member(something(_, _, Object1, _), Inconsistency), member(something(_, _, Object2, _), Inconsistency)
    ;
      member(something(Object1), Inconsistency), member(something(Object2), Inconsistency)
    ),
    % objects are different
    Object1 \== Object2,
    % second criterium: there is a disjunctive axiom with the index Index
    member(axiom(Index), Inconsistency), 
    clauses(Clauses),
    member(satchmo_clause(_Body, Head, [axiom(Index)]), Clauses),
    Head = (_Conjunct ; _Conjuncts)
    ->
    % remove this spurious inconsistency and ...
    select(Inconsistency, Inconsistencies, IntermediateInconsistencies),
    % ... look for additional ones
    remove_spurious_inconsistencies(IntermediateInconsistencies, RestInconsistencies)
  ;
    % no (further) spurious inconsistency
    RestInconsistencies = Inconsistencies
  ).


eliminate_non_minimal_proofs(Proofs, MinimalProofs) :-
  eliminate_non_minimal_proofs(Proofs, Proofs, [], AllMinimalProofs),
  reverse(AllMinimalProofs, MinimalProofs).

eliminate_non_minimal_proofs([], _Proofs, MinimalProofs, MinimalProofs).

eliminate_non_minimal_proofs([proof(ACEAxioms, _AuxiliaryAxioms)|RestProofs], AllProofs, SoFar, MinimalProofs) :-
  (
    % there is a proof using less axioms than the current one
    member(proof(ACEAxioms1, _AuxiliaryAxioms1), AllProofs),
    subset(ACEAxioms1, ACEAxioms), 
    ACEAxioms1 \== ACEAxioms
    ->
    eliminate_non_minimal_proofs(RestProofs, AllProofs, SoFar, MinimalProofs)
  ;
    % there is no smaller proof, keep the current one with empty list of auxiliary axioms
    eliminate_non_minimal_proofs(RestProofs, AllProofs, [proof(ACEAxioms, [])|SoFar], MinimalProofs)
  ).

    
convert_indices_to_sentences(Indices, AllACEAxioms, SubsetOfAxioms) :-
  reverse(Indices, ReversedIndices),
  convert_indices_to_sentences(ReversedIndices, AllACEAxioms, [], [], SubsetOfAxioms).
  
convert_indices_to_sentences([], _AllACEAxioms, ACEAxioms, AuxiliaryAxioms, proof(ACEAxioms, AuxiliaryAxioms)).

convert_indices_to_sentences([Index|RestIndices], AllACEAxioms, ACEAxioms, AuxiliaryAxioms, SubsetOfAxioms) :-
  (
    Index = axiom(I)
    ->
    % skip index of accessibility relation and index 0 introduced for artificially created object/7 definitions of proper names
    (
      (I = accessibility_relation ; I = 0)
      ->
      convert_indices_to_sentences(RestIndices, AllACEAxioms, ACEAxioms, AuxiliaryAxioms, SubsetOfAxioms)
    ;
      nth1(I, AllACEAxioms, Axiom),
      atomic_list_concat([I, Axiom], ': ', NumberedAxiom),
      convert_indices_to_sentences(RestIndices, AllACEAxioms, [NumberedAxiom|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
    )
  ;
    % skip index of theorem
    Index = theorem(_I)
    ->
    convert_indices_to_sentences(RestIndices, AllACEAxioms, ACEAxioms, AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = prolog_axiom(I)
    ->
    % show texts of auxiliary axioms
    prolog_axiom_text(I, PrologAxiomText),  
    convert_indices_to_sentences(RestIndices, AllACEAxioms, ACEAxioms, [PrologAxiomText|AuxiliaryAxioms], SubsetOfAxioms)
  ;
    Index = fol_axiom(I)
    ->
    % show texts of auxiliary axioms
    fol_axiom(I, _Formula, FOLAxiomText), 
    convert_indices_to_sentences(RestIndices, AllACEAxioms, ACEAxioms, [FOLAxiomText|AuxiliaryAxioms], SubsetOfAxioms)
  ;
    Index = who(Name)
    ->
    % show named substitution for query word 'who'
    atomic_list_concat(['Substitution: ', who, ' = ', Name], Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = whose(Name)
    ->
    % show named substitution for query word 'whose'
    atomic_list_concat(['Substitution: ', whose, ' = ', Name], Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
   ;
    Index = what(List), 
    is_list(List) 
    ->
    % show list contents substitution for query word 'what'
    term_to_atom(List, ListAsAtom),
    atomic_list_concat(['Substitution: ', what, ' = ', ListAsAtom], Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
 ;
    Index = what(Name), 
    \+ is_list(Name)
    ->
    % show named substitution for query word 'what'
    atomic_list_concat(['Substitution: ', what, ' = ', Name], Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = somebody(Name)
    ->
    % show named substitution for 'somebody'
    atomic_list_concat(['Substitution: ', somebody, ' = ', Name], Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = something(Name)
    ->
    % show named substitution for 'something'
    atomic_list_concat(['Substitution: ', something, ' = ', Name], Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = who(Op, Count, Who, Details)
    ->
    % show countable common noun substitution for query word 'who'
    translate_op_to_ace(Op, ACEOp),
    atomic_list_concat(['Substitution: ', who, ' = ', '(', ACEOp, ' ', Count, ')', ' ', Who], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = whose(Op, Count, Whose, Details)
    ->
    % show countable common noun substitution for query word 'whose'
    translate_op_to_ace(Op, ACEOp),
    atomic_list_concat(['Substitution: ', whose, ' = ', '(', ACEOp, ' ', Count, ')', ' ', Whose], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = what(Op, Count, What, Details)
    ->
    % show countable common noun substitution for query word 'what'
    translate_op_to_ace(Op, ACEOp),
    atomic_list_concat(['Substitution: ', what, ' = ', '(', ACEOp, ' ', Count, ')', ' ', What], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = how_many(Op, Count, na, Details)
    ->
    % show countable common noun substitution for query word 'how many'
    translate_op_to_ace(Op, ACEOp),
    atomic_list_concat(['Substitution: ', 'how many', ' = ', '(', ACEOp, ' ', Count, ')'], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = how_much(Op, Details)
    ->
    % show mass common noun substitution for query word 'how much'
    atomic_list_concat(['Substitution: ', 'how much', ' = ', '(', Op, ')'], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = how_much(Op, Count, Measure, Details)
    ->
    % show measurement noun substitution for query word 'how much'
    translate_op_to_ace(Op, ACEOp),
    atomic_list_concat(['Substitution: ', 'how much', ' = ', '(', ACEOp, ' ', Count, ' ', Measure, ')'], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = which(Op, Count, Which, Details)
    ->
    % show countable common noun substitution for query word 'which'
    translate_op_to_ace(Op, ACEOp),
    atomic_list_concat(['Substitution: ', which, ' = ', '(', ACEOp, ' ', Count, ')', ' ', Which], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = somebody(Op, Count, Somebody, Details)
    ->
    % show countable common noun substitution for 'somebody'
    translate_op_to_ace(Op, ACEOp),
    atomic_list_concat(['Substitution: ', somebody, ' = ', '(', ACEOp, ' ', Count, ')', ' ', Somebody], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = something(Op, Count, Something, Details)
    ->
    % show countable common noun substitution for 'somebody'
    translate_op_to_ace(Op, ACEOp),
    atomic_list_concat(['Substitution: ', something, ' = ', '(', ACEOp, ' ', Count, ')', ' ', Something], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = whose(Whose, Details)
    ->
    % show mass common noun substitution for query word 'whose'
    atomic_list_concat(['Substitution: ', whose, ' = ', '(some) ', Whose], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = what(What, Details)
    ->
    % show mass common noun substitution for query word 'what'
    atomic_list_concat(['Substitution: ', what, ' = ', '(some) ', What], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = which(Which, Details)
    ->
    % show mass common noun substitution for query word 'which'
    atomic_list_concat(['Substitution: ', which, ' = ', '(some) ', Which], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = which(Which)
    ->
    % show proper name substitution for query word 'which'
    atomic_list_concat(['Substitution: ', which, ' = ', Which], Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = how(Degree, Adverb),
    (Degree=pos ; Degree= comp ; Degree= sup)
    ->
    % show adverb substitution for query words 'how', 'when' and 'where'
    expand_degree(Degree, ExpandedDegree),
    atomic_list_concat(['Substitution: ', 'how/when/where', ' = ', '(', ExpandedDegree, ')', ' ', Adverb], Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = how(Preposition, Op, Count, Noun, Details)
    ->
    % show prepositional phrase substitution for query words 'how', 'when' and 'where'
    translate_op_to_ace(Op, ACEOp),
    atomic_list_concat(['Substitution: ', 'how/when/where', ' = ', '(', Preposition, ')', ' ', '(', ACEOp, ' ', Count, ')', ' ', Noun], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = how(Preposition, Noun, Details)
    ->
    % show  prepositional phrase substitution for query words 'how', 'when' and 'where'
    atomic_list_concat(['Substitution: ', 'how/when/where', ' = ', '(', Preposition, ')', ' ', Noun], IntermediateSubstitution),
    add_details(Details, IntermediateSubstitution, Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
  ;
    Index = gcd(GCD),
    integer(GCD)
    ->
    % show substitution for 'gcd'
    atomic_list_concat(['Substitution: ', gcd, ' = ', GCD], Substitution),
    convert_indices_to_sentences(RestIndices, AllACEAxioms, [Substitution|ACEAxioms], AuxiliaryAxioms, SubsetOfAxioms)
    ).


add_details([], Substitution, Substitution).
  
add_details([Detail|Details], SoFar, Substitution) :-
  (
    Detail=property(Degree, Adjective)
    -> 
    expand_degree(Degree, ExpandedDegree),
    atomic_list_concat([SoFar, ', ', '(', ExpandedDegree, ')', ' ', Adjective], IntermediateSubstitution)
  ;
    Detail = text(Text, List)
    ->
    term_to_atom(List, ListAsAtom), 
    atomic_list_concat([SoFar, ', ', Text, ListAsAtom], IntermediateSubstitution)
  ),
  add_details(Details, IntermediateSubstitution, Substitution).


expand_degree(pos, 'positive of').
expand_degree(comp, 'comparative of').
expand_degree(sup, 'superlative of').


%---------------------------------------------------------------------------------------------------------
%
%  why_not(+Clauses, +Models, -WhyNot)
%
%  find out which part WhyNot of the theorem/query - located in Clauses - is not covered by the elements 
%  of any of the Models generated from the axioms
%
%  deriving theorems/queries from axioms generate minimal abducted set of axioms to cover theorems/queries
%
%---------------------------------------------------------------------------------------------------------

why_not(Clauses, Models, WhyNot) :-
  % get the unique elements of all models
  append(Models, AllModels),
  list_to_set(AllModels, AllModelElements), 
  % model elements have the form (ModelElement, Indices)
  % remove Indices
  findall(ModelElement, member((ModelElement, _Indices), AllModelElements), PureModelElements),
  % convert marked copula 'be_MOD', 'be_ADJ', 'be_ID' and 'be_NP' to 'be' to avoid copula listed as uncovered
  convert_marked_copula(PureModelElements, ConvertedPureModelElements),
  % determine missing coverage
  why_not_for_unique_model_elements(Clauses, ConvertedPureModelElements, WhyNot).


why_not_for_unique_model_elements(Clauses, UniqueModelElements, WhyNot) :-
  % generate list of conditions - different from 'true' and 'fail' - of clauses derived from theorems
  findall(ConditionsList, 
          (
            member(satchmo_clause(Precondition, Consequence, [theorem(_Index)|_]), Clauses),
            \+ Precondition = true,
            conjunction_to_list(Precondition, PreconditionList),
            (
              \+ Consequence = fail
              ->
              conjunction_to_list(Consequence, ConsequenceList)
            ;
              ConsequenceList = []
            ),
            append(PreconditionList, ConsequenceList, ConditionsList)
          ),
          Conditions),
  % convert Conditions - that can be a list of lists - into one list
  flatten(Conditions, FlattenedConditions),
  % convert marked copula 'be_MOD', 'be_ADJ', 'be_ID' and 'be_NP' to 'be' to avoid internally marked copula listed as uncovered
  convert_marked_copula(FlattenedConditions, ConvertedFlattenedConditions),
  % find subset UncoveredConditions of ConvertedFlattenedConditions not covered by UniqueModelElements
  subtract(ConvertedFlattenedConditions, UniqueModelElements, UncoveredConditions),
  % eliminate duplicates
  list_to_set(UncoveredConditions, UniqueUncoveredConditions),
  % convert uncovered conditions to ACE
  findall(ACEWord, (member(UncoveredCondition, UniqueUncoveredConditions), drs_condition_to_ace_words(UncoveredCondition, ACEWord)), UncoveredACEWords),
  % version without abduction
  % for a version with abduction eliminate the next line and activate the section "abduction" below
  WhyNot = UncoveredACEWords.
/*
  % abduction
  (
    % when deriving theorems/queries from axioms generate abducted set of axioms to cover theorems/queries
    nb_getval(global_parameters, Parameters),
    (memberchk(prove, Parameters) ; memberchk(answer_query, Parameters))
    ->
    generate_abducted_set_of_axioms(Clauses, Abduction),
    (
      Abduction \= []
      ->
      append(UncoveredACEWords, Abduction, WhyNot)   
    ;
      append(UncoveredACEWords, ['no abducted axioms'], WhyNot)    
    )
  ;
    % no abduction for consistency checking
    WhyNot = UncoveredACEWords
  ).
*/  
    
convert_marked_copula([], []).

convert_marked_copula([Condition|Conditions], [ConvertedCondition|ConvertedConditions]) :-
  (
    Condition = predicate(World, Referent1, be_MOD, Referent2, Referent3)
    ->
    ConvertedCondition = predicate(World, Referent1, be, Referent2, Referent3)
  ;
    Condition = predicate(World, Referent1, be_ADJ, Referent2, Referent3)
    ->
    ConvertedCondition = predicate(World, Referent1, be, Referent2, Referent3)
  ;
    Condition = predicate(World, Referent1, be_ID, Referent2, Referent3)
    ->
    ConvertedCondition = predicate(World, Referent1, be, Referent2, Referent3)
  ;
    Condition = predicate(World, Referent1, be_NP, Referent2, Referent3)
    ->
    ConvertedCondition = predicate(World, Referent1, be, Referent2, Referent3)
  ;
    ConvertedCondition = Condition
  ),
  convert_marked_copula(Conditions, ConvertedConditions).


generate_abducted_set_of_axioms(Clauses, Abductions) :-
  % replace object definitions of proper names by respective arguments in other conditions
  % see drs_to_fol/make_proper_names_explicit for the reverse replacement introduced before 
  replace_object_definitions_of_proper_names(Clauses, NewClauses),
  !,
  % find all axiom clauses
  findall(satchmo_clause(Body, Head, [axiom(Index)]), member(satchmo_clause(Body, Head, [axiom(Index)]), NewClauses), AxiomClauses),
  % find all abducted axioms
  findall(Abduction, (
						% find a theorem
						member(satchmo_clause(BodyT, fail, [theorem(_)|_]), NewClauses),
						!,
						% select an implication from the axioms where the precondition is not true and the consequence is not fail
						select(satchmo_clause(BodyA, HeadA, [axiom(_)|_]), AxiomClauses, RestAxiomClauses),
						BodyA \= true,
						HeadA \= fail,
						% fix variables to preserve variable consistency
						numbervars(HeadA, 1, _),
						% failing theorem is a subset of the consequence of the implication, or for anaphoric references ...
						% ... like in 'If there is a man then he sleeps.' of the precondition of the implication, or ...
						% ... like in 'There is a man. If the man is tired then he sleeps.' of one of the original axioms
						% transform BodyT into a list BodyTList
						conjunction_to_list(BodyT, BodyTList),
						% transform BodyA into a list BodyAList
						conjunction_to_list(BodyA, BodyAList),
						% transform HeadA into a list HeadAList
						conjunction_to_list(HeadA, HeadAList),						
						forall(member(Sub, BodyTList), (member(Sub, HeadAList) -> true ; subterm(Sub, AxiomClauses))), 
						% temporarily transform BodyAList into satchmo clauses to ...
						findall(satchmo_clause(true, Head, [axiom(_)]), member(Head, BodyAList), BodyAClauses),
						% ... check that the axiom to be abducted and the rest of the axioms are consistent
						append(BodyAClauses, RestAxiomClauses, TestAxiomClauses),
						satchmo(TestAxiomClauses, _Model, Inconsistencies),
						% consistent
						Inconsistencies = [],
						% remove from BodyAList elements that would lead to abducted clauses that are already in RestAxiomClauses
						findall(MBodyAList, (member(MBodyAList, BodyAList), \+ member(satchmo_clause(true, MBodyAList, [axiom(_)]), RestAxiomClauses)), UniqueBodyAList),
						% to create abducted axiom ...
						% ... remove World argument introduced in drs_to_fol ...
						findall(NewMBodyA -_, (  
						                        member(MBodyA, UniqueBodyAList), 
						                        MBodyA =.. [Functor, _World | RestMBodyA],
						                        NewMBodyA =.. [Functor | RestMBodyA]
						                     ), 
						        NewBodyA
						       ),
						% ... then replace geq by eg 
						% see drs_to_fol/map_eq_geq for the reverse replacement introduced before...
						findall(NewM, 
						             (
						               member(M, NewBodyA),
						               (
						                 M = object(Referent, Noun, Quantity, Unit, geq, Count) - Index 
						                 ->
						                 NewM = object(Referent, Noun, Quantity, Unit, eq, Count) - Index
						               ;
						                 NewM = M
						               )
						             ),
						        FinalBodyA), 
					    % ... then undo variable fixing ...
					    varnumbers(FinalBodyA, CopyFinalBodyA),
					    % ... then collect variables ...
					    term_variables(CopyFinalBodyA, Vars),
					    % ... then verbalise ...
						drs_to_ace(drs(Vars, CopyFinalBodyA), [AbductedAxiomsList|_]), 
						% ... then get abducted axioms
						atomic_list_concat(AbductedAxiomsList, ' ', AbductedAxioms),
						atom_concat('abducted axiom to prove the theorem: ', AbductedAxioms, Abduction)
      				 ),
      	  Abductions).


replace_object_definitions_of_proper_names(Clauses, NewClauses) :-
  (  
    % find all object definitions of proper names
    subterm(object(_World, SK, Name, named, na, eq, 1), Clauses),
    % referent SK is either a variable or a skolem function
    (var(SK) ; functor(SK, F, _), term_to_atom(F, A), atom_chars(A, [s, k |_]))
    ->
    % replace referent SK to the proper name Name in all other conditions by named(Name)
    substitute(SK, named(Name), Clauses, IntermediateClauses),
    replace_object_definitions_of_proper_names(IntermediateClauses, NewClauses)
  ;
    % remove now superfluous object definition of proper names introduced in axioms
    (
      select(satchmo_clause(_, _, [axiom(0)]), Clauses, IntermediateClauses1) 
    ; 
      IntermediateClauses1 = Clauses
    ),
    % remove now superfluous object definitions of proper names introduced in theorems
    (
      % find a theorem clause whose body contains object definitions of proper names
      select(satchmo_clause(Body, fail, Index), IntermediateClauses1, IntermediateClauses2), 
      select(theorem(0), Index, NewIndex)
      ->
      % delete these object definitions
      conjunction_to_list(Body, BodyAsList),
      delete(BodyAsList, object(_World, named(Name), Name, named, na, eq, 1), NewBodyAsList),
      list_to_conjunction(NewBodyAsList, NewBody),
      NewClauses = [satchmo_clause(NewBody, fail, NewIndex) | IntermediateClauses2]
    ;
      NewClauses = Clauses
    )
  ).


drs_condition_to_ace_words(Condition, ACEWords) :-
  (
    ( Condition = query(_, _, how) ; Condition = query(_, _, when) ; Condition = query(_, _, where))
    ->
    ACEWords = 'check wether the query how/when/where can be answered from an adverb or prepositional phrase within the axioms'
  ;
    Condition = accessibility_relation(_, _)
    ->
    ACEWords = 'modal operator or sentence subordination'
  ;
    Condition = object(_World, _Ref, Noun, countable, na, eq, 1)
    ->
    atomic_list_concat(['countable common noun: (a/the) ', Noun], ACEWords)
  ;
    Condition = object(_World, _Ref, Noun, countable, Unit, eq, Count)
    ->
    (
      Noun = na,
      Unit = na
      -> 
      ACEWords = 'conjunctive noun phrase'
    ;
      Unit = na 
      -> 
      atomic_list_concat(['countable common noun: (', Count, ') ', Noun], ACEWords)
    ;
      atomic_list_concat(['countable common noun: (', Count, ' ', Unit, ' of) ', Noun], ACEWords)
    )
  ;
    Condition = object(_World, _Ref, Noun, countable, Unit, Op, Count),
    \+ Noun = na
    ->
    translate_op_to_ace(Op, ACEOp),
    (
      Unit = na 
      -> 
      % if the countable common noun was introduced by "how many" then fol_to_clauses/2 replaced the  
      % original count 2 by a variable; undo this here to avoid an exception of atomic_list_concat/2
      (var(Count) -> Count = 2 ; true),
      atomic_list_concat(['countable common noun: (', ACEOp, ' ', Count, ') ', Noun], ACEWords)
    ;
      atomic_list_concat(['countable common noun: (', ACEOp, ' ', Count, ' ', Unit, ' of) ', Noun], ACEWords)
    )
  ;
    Condition = object(_World, _Ref, Noun, mass, na, na, na)
    ->
    atomic_list_concat(['mass common noun: (some) ', Noun], ACEWords)
  ;
    Condition = object(_World, _Ref, Noun, mass, Unit, Op, Count)
    ->
    translate_op_to_ace(Op, ACEOp),
    (
      ACEOp = ''
      ->
      atomic_list_concat(['mass common noun: (', Count, ' ', Unit, ' of) ', Noun], ACEWords)
    ;
      atomic_list_concat(['mass common noun: (', ACEOp, ' ', Count, ' ', Unit, ' of) ', Noun], ACEWords)
    )
  ;
    Condition = object(_World, _Ref, Noun, named, _Unit, _Op, _Count)
    ->
    atomic_list_concat(['proper name: ', Noun], ACEWords)
  ;
    Condition = object(_World, _Ref, Noun, dom, _Unit, _Op, _Count)
    ->
    atomic_list_concat(['indefinite pronoun: ', Noun], ACEWords)
   ;
    Condition = property(_World, _Ref, Adjective, pos)
    ->
    atomic_list_concat(['adjective: ', Adjective], ACEWords)
  ;
    Condition = property(_World, _Ref1, Adjective, pos, Ref2)
    ->
    atomic_list_concat(['adjective: ', Adjective], ACEWord),
    translate_term_to_ACE(Ref2, ACERef2),
    flatten([ACEWord, ACERef2], [ACEWords])
  ;
    Condition = property(_World, _Ref1, Adjective, pos_as, Ref2)
    ->
    atomic_list_concat(['adjective embedded by "as ... as": ', Adjective], ACEWord),
    translate_term_to_ACE(Ref2, ACERef2),
    flatten([ACEWord, ACERef2], [ACEWords])
  ;
    Condition = property(_World, _Ref1, Adjective, Ref2, pos_as, Subj_Obj, Ref3)
    ->
    atomic_list_concat(['adjective embedded by "as ... as": ', Adjective], ACEWord),
    translate_term_to_ACE(Ref2, ACERef2),
    translate_term_to_ACE(Subj_Obj, ACESubj_Obj),
    translate_term_to_ACE(Ref3, ACERef3),
    flatten([ACEWord, ACERef2, ACESubj_Obj, ACERef3], [ACEWords])
  ;
    Condition = property(_World, _Ref, Adjective, comp)
    ->
    atomic_list_concat(['comparative of adjective: ', Adjective], ACEWords)
  ;
    Condition = property(_World, _Ref1, Adjective, comp, Ref2)
    ->
    atomic_list_concat(['comparative of adjective: ', Adjective], ACEWord),
    translate_term_to_ACE(Ref2, ACERef2),
    flatten([ACEWord, ACERef2], [ACEWords])
  ;
    Condition = property(_World, _Ref1, Adjective, comp_than, Ref2)
    ->
    atomic_list_concat(['comparative of adjective followed by "than": ', Adjective], ACEWord),
    translate_term_to_ACE(Ref2, ACERef2),
    flatten([ACEWord, ACERef2], [ACEWords])
  ;
    Condition = property(_World, _Ref1, Adjective, Ref2, comp_than, Subj_Obj, Ref3)
    ->
    atomic_list_concat(['comparative of adjective followed by "than": ', Adjective], ACEWord),
    translate_term_to_ACE(Ref2, ACERef2),
    translate_term_to_ACE(Subj_Obj, ACESubj_Obj),
    translate_term_to_ACE(Ref3, ACERef3),
    flatten([ACEWord, ACERef2, ACESubj_Obj, ACERef3], [ACEWords])
  ;
    Condition = property(_World, _Ref, Adjective, sup)
    ->
    atomic_list_concat(['superlative of adjective: ', Adjective], ACEWords)
  ;
    Condition = property(_World, _Ref1, Adjective, sup, Ref2)
    ->
    atomic_list_concat(['superlative of adjective: ', Adjective], ACEWord),
    translate_term_to_ACE(Ref2, ACERef2),
    flatten([ACEWord, ACERef2], [ACEWords])
  ;
    Condition = relation(_World, _Ref1, Noun, of, Ref2)
    ->
    atomic_list_concat(['genitive: ', Noun, ' of'], ACEWord),
    translate_term_to_ACE(Ref2, ACERef2),
    flatten([ACEWord, ACERef2], [ACEWords])
  ;
    Condition = predicate(_World, _Ref, Verb, SubjRef),
    Verb \= be
    ->
    atomic_list_concat(['intransitive verb: ', Verb], ACEWord),
    translate_term_to_ACE(SubjRef, ACESubjRef),
    flatten([ACEWord, ACESubjRef], [ACEWords])
  ;
    Condition = predicate(_World, _Ref, be, SubjRef)
    ->
    atomic_list_concat(['copula: ', 'is/are'], ACEWord),
    translate_term_to_ACE(SubjRef, ACESubjRef),
    flatten([ACEWord, ACESubjRef], [ACEWords])
  ;
    Condition = predicate(_World, _Ref, Copula, SubjRef, ObjRef),
    (Copula = be ; Copula = be_MOD ; Copula = be_ID ; Copula = be_NP ; Copula = be_ADJ ; Copula = be_NUM)
    ->
    atomic_list_concat(['copula: ', 'is/are'], ACEWord),
    translate_term_to_ACE(SubjRef, ACESubjRef),
    translate_term_to_ACE(ObjRef, ACEObjRef),
    flatten([ACEWord, ACESubjRef, ACEObjRef], [ACEWords])
  ;
    Condition = predicate(_World, _Ref, Verb, SubjRef, ObjRef)
    ->
    atomic_list_concat(['transitive verb: ', Verb], ACEWord),
    translate_term_to_ACE(SubjRef, ACESubjRef),
    translate_term_to_ACE(ObjRef, ACEObjRef),
    flatten([ACEWord, ACESubjRef, ACEObjRef], [ACEWords])
  ;
    Condition = predicate(_World, _Ref, Verb, SubjRef, ObjRef, IndObjRef)
    ->
    atomic_list_concat(['ditransitive verb: ', Verb], ACEWord),
    translate_term_to_ACE(SubjRef, ACESubjRef),
    translate_term_to_ACE(ObjRef, ACEObjRef),
    translate_term_to_ACE(IndObjRef, ACEIndObjRef),
    flatten([ACEWord, ACESubjRef, ACEObjRef, ACEIndObjRef], [ACEWords])
  ;
    Condition =  modifier_adv(_World, _Ref, Adverb, pos)
    ->
    atomic_list_concat(['adverb: ', Adverb], ACEWords)
  ;
    Condition =  modifier_adv(_World, _Ref, Adverb, comp)
    ->
    atomic_list_concat(['comparative of adverb: ', Adverb], ACEWords)
  ;
    Condition =  modifier_adv(_World, _Ref, Adverb, sup)
    ->
    atomic_list_concat(['superlative of adverb: ', Adverb], ACEWords)
  ;
    Condition =  modifier_pp(_World, _Ref1, Preposition, Ref2)
    ->
    atomic_list_concat(['preposition: ', Preposition], ACEWord),
    translate_term_to_ACE(Ref2, ACERef2),
    flatten([ACEWord, ACERef2], [ACEWords])
  ).

translate_op_to_ace(eq, '=').
translate_op_to_ace(geq, 'at least').
translate_op_to_ace(greater, 'more than').
translate_op_to_ace(exactly, 'exactly').
translate_op_to_ace(leq, 'at most').
translate_op_to_ace(less, 'less than').

translate_term_to_ACE(Term, ACETerm) :-
  (
    % Term is a variable
    var(Term)
    ->
    ACETerm = []
  ;
    % Term is skolem constant or function
    functor(Term, Functor, _Arity),
    \+ Functor = [],
    sub_atom(Functor, 0, _, _, sk)
    ->
    ACETerm = []
  ;
    % Term is a named item
    Term = named(Name)
    ->
    atomic_list_concat(['proper name: ', Name], ACETerm)
  ;
    % Term is an integer
    Term = int(Integer)
    ->
    atomic_list_concat(['integer: ', Integer], ACETerm)
  ;
    % Term is a real
    Term = real(Real)
    ->
    atomic_list_concat(['real: ', Real], ACETerm)
  ;
    % Term is a string
    Term = string(String)
    ->
    atomic_list_concat(['string: ', String], ACETerm)
  ;
    % Term is a list
    Term = list(List)
    ->
    term_to_atom(List, ListAsAtom),
    atomic_list_concat(['list: ', ListAsAtom], ACETerm)
  ;
    % Term is a set
    Term = set(Set)
    ->
    term_to_atom(Set, SetAsAtom),
    atomic_list_concat(['set: ', SetAsAtom], ACETerm)
  ).


%---------------------------------------------------------------------------------------------------------
%
%  time(+Procedure, -RunTime)
%
%  RunTime is the time in ms to run Procedure
%
%---------------------------------------------------------------------------------------------------------

time(Procedure, RunTime) :-
  statistics(runtime, _),
  call(Procedure),
  statistics(runtime, [_, RunTime]).


%---------------------------------------------------------------------------------------------------------
%
%  clean up from previous run
%    
%  remove all global variables
%  retract all asserted predicates
%  reset global parameters
%  remove all messages
%
%---------------------------------------------------------------------------------------------------------

clean_up :-
  forall(nb_current(Name, _Value), nb_delete(Name)),
  nb_setval(global_parameters, []),
  user:retractall(axioms_theorems(_, _)),
  user:retractall(clauses(_)),
  user:retractall(axioms(_)),
  user:retractall(theorems(_)),
  user:retractall(indices(_, _)),
  user:retractall(object(_, _, _, _, _, _, _)),
  user:retractall(property(_, _, _, _)),
  user:retractall(property(_, _, _, _, _)),
  user:retractall(property(_, _, _, _, _, _, _)),
  user:retractall(relation(_, _, _, _, _)),
  user:retractall(predicate(_, _, _, _)),
  user:retractall(predicate(_, _, _, _, _)),
  user:retractall(predicate(_, _, _, _, _, _)),
  user:retractall(modifier_adv(_, _, _, _)),
  user:retractall(modifier_pp(_, _, _, _)),
  user:retractall(has_part(_, _, _)),
  user:retractall(query(_, _, _)),
  user:retractall(formula(_, _, _, _)),
  user:retractall(accessibility_relation(_, _)),
  retractall(user:identical_named_objects(_, _, _)),
  clear_messages.
  
  
%---------------------------------------------------------------------------------------------------------
