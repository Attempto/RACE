:- use_module('../prolog/race').

env_ns('http://schemas.xmlsoap.org/soap/envelope/').
% TODO: make configurable
race_ns('http://attempto.ifi.uzh.ch/race').


run_race :-
	catch(
		call_with_time_limit(20, run_race_x),
		CatchType,
		(
			create_error_soap_message(CatchType, SOAPOutput),
		    format(user_error, 'REPLY:\n~w\n\n', SOAPOutput),
		    format('~w\n', SOAPOutput)
		)
	).


run_race_x :-
    prompt(_, ''),
    read_stream_to_codes(user_input, SOAPInputCodes),
    atom_codes(SOAPInput, SOAPInputCodes),
    format(user_error, 'REQUEST:\n~w\n\n', SOAPInput),
    atom_to_memory_file(SOAPInput, InHandle),
    open_memory_file(InHandle, read, In),
    load_structure(stream(In), Message, [dialect(xmlns)]),
    close(In),
    free_memory_file(InHandle),
    get_element(Message, 'Envelope', Envelope),
    get_element(Envelope, 'Body', Body),
    get_element(Body, 'Request', element(_, _, Request)),
    process(Request, Reply),
    race_ns(RaceNS),
    create_soap_message(element(RaceNS:'Reply', [], Reply), SOAPOutput),
    format(user_error, 'REPLY:\n~w\n\n', SOAPOutput),
    format('~w\n', SOAPOutput),
    !.

run_race_x :-
	create_error_soap_message('Invalid request', SOAPOutput),
    format(user_error, 'REPLY:\n~w\n\n', SOAPOutput),
    format('~w\n', SOAPOutput).


process(Request, Reply) :-
    get_element(Request, 'Mode', element(_, _, ['check_consistency'])),
    get_element(Request, 'Axioms', element(_, _, [Axioms])),
    findall(Parameter, get_element(Request, 'Parameter', element(_, _, [Parameter])), Parameters),
    check_consistency(Axioms, Parameters, Messages, Runtime, Proofs),
    transform_messages(Messages, MessagesX),
    atom_number(RuntimeA, Runtime),
    generate_proof_elements(Proofs, ProofElements),
    race_ns(RaceNS),
    append(MessagesX, [element(RaceNS:'Runtime', [], [RuntimeA])|ProofElements], Reply).

process(Request, Reply) :-
    get_element(Request, 'Mode', element(_, _, [prove])),
    get_element(Request, 'Axioms', element(_, _, [Axioms])),
    get_element(Request, 'Theorems', element(_, _, [Theorems])),
    findall(Parameter, get_element(Request, 'Parameter', element(_, _, [Parameter])), Parameters),
    prove(Axioms, Theorems, Parameters, Messages, Runtime, Proofs, WhyNot),
    transform_messages(Messages, MessagesX),
    atom_number(RuntimeA, Runtime),
    generate_proof_elements(Proofs, ProofElements),
    generate_whynot_elements(WhyNot, WhyNotElements),
    race_ns(RaceNS),
    WhyNotElement = element(RaceNS:'WhyNot', [], WhyNotElements),
    append(MessagesX, [element(RaceNS:'Runtime', [], [RuntimeA])|ProofElements], ReplyTemp),
    append(ReplyTemp, [WhyNotElement], Reply).

process(Request, Reply) :-
    get_element(Request, 'Mode', element(_, _, [answer_query])),
    get_element(Request, 'Axioms', element(_, _, [Axioms])),
    get_element(Request, 'Theorems', element(_, _, [Theorems])),
    findall(Parameter, get_element(Request, 'Parameter', element(_, _, [Parameter])), Parameters),
    answer_query(Axioms, Theorems, Parameters, Messages, Runtime, Proofs, WhyNot),
    transform_messages(Messages, MessagesX),
    atom_number(RuntimeA, Runtime),
    generate_proof_elements(Proofs, ProofElements),
    generate_whynot_elements(WhyNot, WhyNotElements),
    race_ns(RaceNS),
    WhyNotElement = element(RaceNS:'WhyNot', [], WhyNotElements),
    append(MessagesX, [element(RaceNS:'Runtime', [], [RuntimeA])|ProofElements], ReplyTemp),
    append(ReplyTemp, [WhyNotElement], Reply).


transform_messages([], []).

transform_messages([MessageIn|RestIn], [MessageOut|RestOut]) :-
    MessageIn = message(Importance, Type, Pos, Subject, Description),
    ( Pos = SentenceID-_ ; SentenceID = '' ),
    ( number(SentenceID), atom_number(Sentence, SentenceID) ; Sentence = SentenceID ),
    race_ns(RaceNS),
    MessageOut = element(RaceNS:'Message', [], [
    	element(RaceNS:'Importance', [], [Importance]),
    	element(RaceNS:'Type', [], [Type]),
    	element(RaceNS:'SentenceID', [], [Sentence]),
    	element(RaceNS:'Subject', [], [Subject]),
    	element(RaceNS:'Description', [], [Description])
    ]),
    transform_messages(RestIn, RestOut).


generate_proof_elements([], []).

generate_proof_elements([proof(Axioms,AuxAxioms)|RestIn], [ProofElement|RestOut]) :-
    race_ns(RaceNS),
    generate_axiom_elements(Axioms, AxiomElements),
    generate_auxaxiom_elements(AuxAxioms, AuxAxiomElements),
    ProofElement1 = element(RaceNS:'UsedAxioms', [], AxiomElements),
    ProofElement2 = element(RaceNS:'UsedAuxAxioms', [], AuxAxiomElements),
    ProofElement = element(RaceNS:'Proof', [], [ProofElement1, ProofElement2]),
    generate_proof_elements(RestIn, RestOut).


generate_axiom_elements([], []).

generate_axiom_elements([Axiom|RestIn], [AxiomElement|RestOut]) :-
    race_ns(RaceNS),
    AxiomElement = element(RaceNS:'Axiom', [], [Axiom]),
    generate_axiom_elements(RestIn, RestOut).


generate_auxaxiom_elements([], []).

generate_auxaxiom_elements([AuxAxiom|RestIn], [AuxAxiomElement|RestOut]) :-
    race_ns(RaceNS),
    AuxAxiomElement = element(RaceNS:'AuxAxiom', [], [AuxAxiom]),
    generate_auxaxiom_elements(RestIn, RestOut).


generate_whynot_elements([], []).

generate_whynot_elements([Word|RestIn], [WordElement|RestOut]) :-
    race_ns(RaceNS),
    WordElement = element(RaceNS:'Word', [], [Word]),
    generate_whynot_elements(RestIn, RestOut).


%% get_element(+XMLStructure, +ElementName, -Element)
%
% Returns an element of XMLStructure that has the name ElementName. XMLStructure can be an
% XML element like element(_,_,_), or it can be a list of XML elements. The predicate
% returns all solutions, if backtracking is forced.
% Only elements that occur on the top-most level are found (shallow search).

get_element(element(_, _, Content), ElementName, Element) :-
    get_element(Content, ElementName, Element).

get_element(XMLList, ElementName, Element) :-
    member(element(NS:ElementName, P, C), XMLList),
    Element = element(NS:ElementName, P, C).

get_element(XMLList, ElementName, Element) :-
    member(element(ElementName, P, C), XMLList),
    ElementName \= _:_,
    Element = element(ElementName, P, C).


%% create_soap_message(+Content, -SOAPMessage)
%
% Generates a complete SOAP message. Content is a Prolog-encoded XML term which is inserted into the
% body-part of the envelope. SOAPMessage is returned as an atom.

create_soap_message(Content, SOAPMessage) :-
    env_ns(EnvNS),
    race_ns(RaceNS),
    SOAPElement =
    	element(EnvNS:'Envelope', [xmlns:env=EnvNS, xmlns:race=RaceNS], [
    		element(EnvNS:'Body', [], [Content])
    	]),
    xmlterm_to_xmlatom(SOAPElement, SOAPMessage).


create_error_soap_message(ErrorText, SOAPMessage) :-
    transform_messages([message(error, ws, ''-'', ErrorText, 'Web service call failed.')], MessagesX),
    race_ns(RaceNS),
    create_soap_message(element(RaceNS:'Reply', [], MessagesX), SOAPMessage).


xmlterm_to_xmlatom(XMLTerm, XMLAtom) :-
    new_memory_file(MemHandle),
    open_memory_file(MemHandle, write, S),
    xml_write(S, XMLTerm, []),
    close(S),
    memory_file_to_atom(MemHandle, XMLAtom).
