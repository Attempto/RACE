:- use_module(library(http/thread_httpd)).
:- use_module(library(http/http_dispatch)).
:- use_module(library(http/http_parameters)).
:- use_module(library(http/http_files)).
:- use_module(library(http/http_client)).     % for http_read_data/3
:- use_module(library(sgml)).                 % for load_structure/3

:- use_module(racews_api, [
	create_soap_message/2,
	create_error_soap_message/2,
	get_element/3,
	process/2,
	race_ns/1
]).

% Web client (which posts queries to the web service)
%:- http_handler(root(.), http_reply_file('racews.html', []), []).
:-
    %getenv('RACE_HTTPSERVER_FILES_PATH', Path),
    %getenv('RACE_HTTPSERVER_FILES_DIR', Dir),
    %http_handler(Path, http_reply_from_files(Dir, []), [prefix]);
    http_handler(root(.), http_reply_from_files(racews, []), [prefix]);
    true.


% Allow any origin.
% TODO: make configurable on the command-line
%:- set_setting(http:cors, [*]).

% Web service
:- http_handler(root(service/race), race_handler, [method(post)]).

:- dynamic(http_server_time_limit/1).

%% default_value(+Key:atom, -Value:atomic)
%
% Specifies the default values of the commandline parameters.
%
default_value(workers, 4).
default_value(port, 8000).
default_value(timelimit, 30).


%% argument(?Arg, -Value, -Desc)
%
% Command-line arguments.
%
argument('-port', 'NUMBER', 'Override the default port (8000) of the HTTP interface.').
argument('-workers', 'NUMBER', 'Override the default number of workers (4) on the HTTP server.').
argument('-timelimit', 'NUMBER', 'Time out after this number of seconds.').
argument('-version', '', 'Show version information.').
argument('-help', '', 'Show this help page.').


%% main
%
main :-
	get_arglist(ArgList),
	catch(
		( arglist_namevaluelist(ArgList, InputList), process_input(InputList) ),
		Exception,
		format_error_for_terminal(Exception)
	).


%% arglist_namevaluelist(+ArgList:list, -NameValueList:list)
%
% @param ArgList is a list of arguments
% @param NameValueList is a list of ArgumentName=ArgumentValue pairs
%
arglist_namevaluelist([], []).

% If argument comes with no value
arglist_namevaluelist([Arg | Tail1], [Name=on | Tail2]) :-
	argument(Arg, '', _),
	!,
	atom_concat('-', Name, Arg),
	arglist_namevaluelist(Tail1, Tail2).

% Else: argument must have a value
arglist_namevaluelist([Arg, ValueAtom | Tail1], [Name=Value | Tail2]) :-
	argument(Arg, _, _),
	\+ argument(ValueAtom, _, _),
	!,
	atom_concat('-', Name, Arg),
	(
		catch(atom_number(ValueAtom, ValueNumber), _, fail)
	->
		Value = ValueNumber
	;
		Value = ValueAtom
	),
	arglist_namevaluelist(Tail1, Tail2).

arglist_namevaluelist([Arg | _], _) :-
	argument(Arg, _, _),
	!,
	throw(error('Missing value for argument', context(arglist_namevaluelist/2, Arg))).

arglist_namevaluelist([Arg | _], _) :-
	throw(error('Illegal argument', context(arglist_namevaluelist/2, Arg))).


%% process_input(+InputList:list)
%
% @param InputList is a list of input parameters
%
process_input(InputList) :-
	memberchk(help=on, InputList),
	!,
	show_help.

process_input(InputList) :-
	memberchk(version=on, InputList),
	!,
	show_version.

process_input(InputList) :-
	get_arg(port, InputList, Port),
	get_arg(workers, InputList, Workers),
	get_arg(timelimit, InputList, TimeLimit),
	start_http_server(Port, Workers, TimeLimit).


%% get_arg(+Key:atom, +InputList:list, -Value:atomic)
%
% Gets the value of the input parameter if set,
% otherwise uses the default value.
%
get_arg(Key, InputList, Value) :-
	memberchk(Key=Value, InputList),
	!.

get_arg(Key, _, Value) :-
	default_value(Key, Value).


%% show_help
%
% Prints help.
%
show_help :-
	show_version,
	write('Copyright 2025 Kaarel Kaljurand <kaljurand@gmail.com>\n'),
	write('This program comes with ABSOLUTELY NO WARRANTY.\n'),
	write('This is free software, and you are welcome to redistribute it under certain conditions.\n'),
	write('Please visit https://github.com/Attempto/RACE for details.\n'),
	nl,
	write('Command-line arguments:\n'),
	argument(Arg, Value, Desc),
	\+ Desc = hidden,
	format('~w ~w~20|~w~n', [Arg, Value, Desc]),
	fail ; true.


%% show_version
%
% Prints the version information.
%
show_version :-
	format("RACE server, ver ~w~n", ['0.0.1']).


%% get_arglist(-ArgList)
%
% Returns the list of arguments.
% In SWI v6.6.0+ this can be achieved simply by:
%
% get_arglist(ArgList) :-
%	current_prolog_flag(argv, ArgList).
%
% For backwards compatibility we assume that the argument
% list can contain '--' or something (the name of the program)
% before the first flag (which starts with '-').
%
get_arglist(ArgList) :-
	current_prolog_flag(argv, RawArgList),
	get_arglist_x(RawArgList, ArgList).

get_arglist_x(RawArgList, ArgList) :-
	append(_, ['--'|ArgList], RawArgList),
	!.

get_arglist_x(ArgList, Suffix) :-
	get_suffix(ArgList, Suffix).

get_suffix([], []).

get_suffix([Arg | ArgList], [Arg | ArgList]) :-
	atom_concat('-', _, Arg),
	!.

get_suffix([_ | ArgList1], ArgList2) :-
	get_suffix(ArgList1, ArgList2).


%% http_server(+PortNumber:integer, +WorkerCount:integer)
%
% @bug Make sure I understand what thread_get_message/1 does.
%
start_http_server(Port, Workers, TimeLimit) :-
	format("Starting RACE server at port ~w with ~w workers and ~w sec time limit ...~n", [Port, Workers, TimeLimit]),
	assert(http_server_time_limit(TimeLimit)),
	http_server(http_dispatch, [port(Port), workers(Workers)]),
	thread_get_message(_),
	format("Stopping RACE server ...~n"),
	halt.

race_handler(Request) :-
	http_server_time_limit(TimeLimit),
	catch(
		call_with_time_limit(
			TimeLimit,
			(
				http_read_data(Request, RawXml, [to(string)]),
    			setup_call_cleanup(
					open_string(RawXml, Stream),
					load_structure(Stream, Xml, [dialect(xmlns)]),
					close(Stream)
				),
				run_race(Xml)
			)
		),
		Exception,
		(
			create_error_soap_message(Exception, Content),
			format_error_for_http(Exception, ContentType, Content),
			format('Content-type: ~w\r\n\r\n~w', [ContentType, Content])
		)
	).


%% format_error_for_terminal(+Exception:term)
%
% Pretty-prints the exception term for the terminal.
%
% @param Exception is the exception term in the form
%        error(Formal, context(Module:Name/Arity, Message))
%
format_error_for_terminal(error(Formal, context(Predicate, Message))) :-
	!,
	format_message(Message, FMessage),
	format(user_error, "ERROR: ~w: ~w: ~w~n", [Formal, Predicate, FMessage]).

format_error_for_terminal(Error) :-
	format(user_error, "ERROR: ~w~n", [Error]).


%% format_error_for_http(+Exception:term, -ContentType:atom, -Content:term)
%
% Generates an error message from the exception term.
%
% @param Exception is the exception term in the form
%        error(Formal, context(Module:Name/Arity, Message))
% @param ContentType is the content type that message is formated into, e.g. text/xml
% @param Content is the actual error message
%
format_error_for_http(error(Formal, context(Predicate, Message)), 'text/xml', Xml) :-
	!,
	functor(Formal, Name, _),
	format_message(Message, FMessage),
	with_output_to(atom(Xml), format("<error type=\"~w\">~w: ~w: ~w</error>", [Name, Formal, Predicate, FMessage])).

format_error_for_http(Error, 'text/xml', Xml) :-
	with_output_to(atom(Xml), format("<error>~w</error>", [Error])).


%% format_message(+Message:term, -FormattedMessage:atom)
%
format_message(Message, '') :-
	var(Message),
	!.

format_message(Message, Message).


%% set_utf8_encoding(+Stream)
%
% Sets the encoding of the given stream to UTF-8. For some unknown reason, an error is sometimes
% thrown under Windows XP (and Windows 7) when calling set_stream/2, and this error is caught here.

set_utf8_encoding(Stream) :-
	catch(
		set_stream(Stream, encoding(utf8)),
		_,
		true
	).



run_race(Xml) :-
	current_stream(1, write, Stream),
	% TODO: maybe this should not be called at all, because
	% the user should be able to influence the encoding by
	% configuring the environment.
	set_utf8_encoding(Stream),
	format('Content-type: text/xml; charset=UTF-8~n~n'),
	%format('Content-type: ~w\r\n\r\n', ['text/xml']),
	run_race_x(Xml, SoapOutput),
	format("~w~n", [SoapOutput]).


run_race_x(Xml, SoapOutput) :-
	get_element(Xml, 'Envelope', Envelope),
	get_element(Envelope, 'Body', Body),
	get_element(Body, 'Request', element(_, _, Request)),
	process(Request, Reply),
	race_ns(RaceNS),
	create_soap_message(element(RaceNS:'Reply', [], Reply), SoapOutput),
	!.

run_race_x(_, SoapOutput) :-
	create_error_soap_message('Invalid request', SoapOutput).
