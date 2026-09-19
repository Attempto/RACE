%---------------------------------------------------------------------------------------------------------
% 
%  Prolog client for the local APE copy
%
%  N. E. Fuchs
%  University of Zurich
%
%  9 August 2017
% 
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
% 
%  How to?
%
%  open terminal window for folder ape
%  compile APE via [runape] or bash run.sh, and quit APE prompt
%  compile ace_niceace in the same directory: 
%                      ['/Volumes/AllThingsConsidered/Attempto\ Trunk/trunk/ape/utils/ace_niceace.pl'].
%  compile RACE in same directory: ['/Volumes/AllThingsConsidered/Attempto\ Trunk/trunk/race/race.pl'].
% 
%---------------------------------------------------------------------------------------------------------

%---------------------------------------------------------------------------------------------------------
%
%  declarations
%
%---------------------------------------------------------------------------------------------------------

:- module(ape_client, [acetext_to_drs/4]).


%---------------------------------------------------------------------------------------------------------
%
%  acetext_to_drs(+ACEtext, -DRS, -Text, -Messages)
%
%  Example 1
%  ?- acetext_to_drs('A man waits. A woman sleeps.', DRS, Text, Messages).
%
%  DRS = drs([_G3869, _G3872, _G3875, _G3878], [object(_G3869, man, countable, na, eq, 1)-1, predicate(_G3872, wait, _G3869)-1, 
%        object(_G3875, woman, countable, na, eq, 1)-2, predicate(_G3878, sleep, _G3875)-2])
%  Text = ['A man waits.', 'A woman sleeps.']
%  Messages = [] 
% 
%  Example 2
%  ?- acetext_to_drs('A man eates a kitkat.', DRS, Text, Messages).
%  DRS = drs([], [])
%  Text = ['A man eates a kitkat.']
%  Messages = [message(error, sentence, 1-3, 'A man <> eates a kitkat.', 'This is the first sentence that was not ACE. 
%                                                           The sign <> indicates the position where parsing failed.'), 
%              message(error, word, ''-'', kitkat, 'Use the prefix n:, v:, a: or p:.'), 
%              message(error, word, ''-'', eates, eats)]
%
%---------------------------------------------------------------------------------------------------------

acetext_to_drs(ACEtext, DRS, Sentences, Messages) :-
    ace_to_drs:acetext_to_drs(ACEtext, Tokens, _SyntaxTreeList, DRS, Messages),
    % if Tokens contains "but" generate error message
    (
      member(OneTokenList, Tokens),
      memberchk(but, OneTokenList)
      -> 
      race_error_logger:add_error_message_once(race, '', 'Note that RACE does not accept sentences containing the ACE constructs "nothing but/nobody but/no ... but".' , 'Consider rephrasing your input. Example: Replace "Mary likes no man but John." by "Mary likes somebody. Everybody who is liked by Mary is John."')
    ;
      true
    ),
    ace_niceace:tokens_to_sentences(Tokens, Sentences).

%---------------------------------------------------------------------------------------------------------
