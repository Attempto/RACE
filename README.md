# RACE — Reasoning in ACE

## Installation and usage

### Dependencies

- [SWI-Prolog](http://www.swi-prolog.org) (tested with v9.2.8)
- [APE](https://github.com/Attempto/APE) (included as a submodule)
- [Flask](https://flask.palletsprojects.com/), used for the webservice

### Installation

```
$ git clone --recurse-submodules git@github.com:Attempto/RACE.git
$ cd APE
$ make plp

edit prolog/race.pl and comment out ":- check"
```

### Using the webservice

```
$ cd client
$ swipl -o racews.sav -c racews
$ python3 racews.py
```

The RACE webclient is now running on http://127.0.0.1:5000

## Query Modes
```
%---------------------------------------------------------------------------------------------------------
%
%  The Attempto Reasoner RACE offers comprehensive query modes to interrogate an ACE text, concretely
%
%  – yes/no questions constructed with "does/do" and "is/are"
%  – asking for nouns – subjects or objects – with the help of the query words "who" or "what"
%  – identifying nouns via sentences or queries containing "somebody", "someone" or "something"
%  – identifying all nouns via the queries "Who is there?" or "What is there?"
%  – asking for adjectives with the help of the query word "which"
%  – asking for genitives with the help of the query word "whose"
%  – asking for adverbs or preopositional phrases with the query words "how", "when" or "where"
%  – asking for verbs – including the copula – with the help of "does what" or "does do what"
%  – asking for cardinalities or amounts with the help of "how many" or "how much"
%
%---------------------------------------------------------------------------------------------------------
%
%  Two very contrived examples showing a variety of query modes
%
%  Axiom: John's red cat sleeps silently.
%
%  Query: Something does do what how?
%
%  The following minimal subsets of the axioms answer the query:
%
%  Subset 1
%  1: John's red cat sleeps silently on a chair.
%  Substitution: what = sleep
%  Substitution: how/when/where = (positive of) silently
%  Substitution: something = (at least 1) cat, (positive of) red
% 
% 
%  Axiom: The teacher selects two most promising students of the beginner's class for the examination.
% 
%  Query: What is there?
% 
%  The following minimal subsets of the axioms answer the query:
% 
%  Subset 1
%  1: The teacher selects two most promising students of the beginner's class for the examination.
%  Substitution: what = (at least 1) teacher
% 
%  Subset 2
%  1: The teacher selects two most promising students of the beginner's class for the examination.
%  Substitution: what = (at least 2) student, (superlative of) promising
% 
%  Subset 3
%  1: The teacher selects two most promising students of the beginner's class for the examination.
%  Substitution: what = (at least 1) class
% 
%  Subset 4
%  1: The teacher selects two most promising students of the beginner's class for the examination.
%  Substitution: what = (at least 1) beginner
% 
%  Subset 5
%  1: The teacher selects two most promising students of the beginner's class for the examination.
%  Substitution: what = (at least 1) examination
% 
%---------------------------------------------------------------------------------------------------------
```