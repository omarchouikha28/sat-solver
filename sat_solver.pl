:- module(sat_solver,[normalise/2, to_cnf/2, solve/1]).

:- load_test_files([]).

:- use_module(library(lists)).

:- use_module(library(theme/dark)).


%% normalise(+Formula, -NFormula).

% Base case
normalise(lit(X), lit(X)) :- !.

normalise(not(lit(H)), lit(false)) :- H==true.
normalise(not(lit(H)), lit(true)) :-  H==false.

% Normalise conjunction
normalise(and(X, Y), and(NX, NY)) :-
    normalise(X, NX),
    normalise(Y, NY).

% Normalise disjunction
normalise(or(X, Y), or(NX, NY)) :-
    normalise(X, NX),
    normalise(Y, NY).

% Eliminate double negation.
normalise(not(not(X)), NX) :- !, normalise(X,NX).

% Normalise negation (NOT)
normalise(not(X), not(NX)) :-
    !,
    normalise(X, NX).

% Rewrite implication
normalise(implies(X, Y), or(not(NX), NY)) :-
    !,
    normalise(X, NX),
    normalise(Y, NY).

% Rewrite equivalence
normalise(equivalence(X, Y), R) :-
    normalise(X, NX),
    normalise(Y, NY),
    normalise(and(or(not(NX), NY), or(NX, not(NY))), R),
    !.

% Base case
or_all([Var], Var) :- !.

% Construct nested OR expressions
or_all([Head|Tail], or(Rest, Head)) :-
    or_all(Tail, Rest).

% Rewrite the list of vars ([a,b,c] -> or(or(a,b),c))
normalise(min_one_pos(ListOfVars), R) :-
    !,
    or_all(ListOfVars, R).

% Base case
and_all([Var], Var) :- !.

% Construct nested AND expressions
and_all([Head|Tail], and(Rest, Head)) :-
    !,
    and_all(Tail, Rest).

% Makes sure that at most one variable in a list is true
at_most_one_true([], []).
at_most_one_true([Var|Vars], R) :-
    at_most_one_true_clause(Var, Vars, Clause),
    at_most_one_true(Vars, RestR),
    append(Clause, RestR, R).

at_most_one_true_clause(_, [], []).
at_most_one_true_clause(Var1, [Var2|Vars], [or(not(Var1), not(Var2))|Clause]) :-
    at_most_one_true_clause(Var1, Vars, Clause).

% Rewrite the exactly_one_pos rule
normalise(exactly_one_pos(ListOfVars), Result) :-
    at_most_one_true(ListOfVars, R1),
    or_all(ListOfVars, R2),
    append(R1,[R2],Temp),
    and_all(Temp, Result),
    !.

% Refactor the results as demanded in the exercise.

% Base case
to_list(lit(X), [[X]]) :- !.
to_list_negation_helper(lit(X), X) :- !.

% Makes sure that the negation is shown in the final results.
to_list(not(X), [[not(NX)]]) :- 
    !,
    to_list_negation_helper(X, NX).

% Refactors the disjunction
to_list(or(X,Y), [R]) :- 
    !,
    to_list(X, NX), 
    to_list(Y, NY),
    flatten([NX, NY], R).

% Refactors the conjunction
to_list(and(X,Y), R) :- 
    !,
    to_list(X, NX),
    to_list(Y, NY),
    append(NX, NY, R).

%% to_cnf(+Formula, -CNF).
to_cnf([], [[]]) :- !.
to_cnf(lit(X), [[X]]) :- !.
to_cnf(not(lit(X)), [[not(X)]]) :- !.

to_cnf(_Formula, _CNF) :-
    !,
    normalise(_Formula, _NFormula),
    de_morgan(_NFormula, _MFormula),
    distribution(_MFormula, _CFormula),
    to_list(_CFormula, _CNF).


% Distribute OR over AND (A ∨ (B ∧ C) becomes (A ∨ B) ∧ (A ∨ C))

% Base case
distribution(lit(X), lit(X)) :- !.

distribution(not(P), not(P)) :- 
    !,
    distribution(P,P).

distribution(or(P, and(Q,R)), and(CNF1, CNF2)) :-
    !,
    distribution(or(P,Q), CNF1),
    distribution(or(P,R), CNF2).

distribution(or(and(P,Q), R), and(CNF1, CNF2)) :- 
    !,
    distribution(or(P,R), CNF1),
    distribution(or(Q,R), CNF2).       

distribution(and(P,Q), and(CNF1, CNF2)) :- 
    !,
    distribution(P, CNF1),
    distribution(Q, CNF2).

distribution(or(P,Q), or(CNF1,CNF2)) :- 
    !,
    distribution(P, CNF1),
    distribution(Q, CNF2).
 

% De Morgans Law

de_morgan(not(not(A)), R) :- 
    !,
    de_morgan(A, R).

de_morgan(not(or(A,B)), R) :-
    !,
    de_morgan(and(not(A), not(B)), R).

de_morgan(not(and(A,B)), R) :- 
    !,
    de_morgan(or(not(A), not(B)), R).

de_morgan(and(A,B), and(R1,R2)) :- 
    !, 
    de_morgan(A,R1),
    de_morgan(B,R2).

de_morgan(or(A,B), or(R1,R2)) :- 
    !, 
    de_morgan(A,R1), 
    de_morgan(B,R2).

de_morgan(A, A).    

%% solve(+CNF).
solve(_CNF) :-
    !,
    reformat_input(_CNF, FormattedCNF),
    dpll(FormattedCNF, [], Model),
    maplist(convert_variables(), Model, Nm).


convert_variables(pos(true), true) :- !.
convert_variables(neg(false), false) :- !.
convert_variables(neg(X), false).
convert_variables(pos(X), true).

% Negates a given literal
negate(true, false).
negate(false, true).
negate(pos(A), neg(A)).
negate(neg(A), pos(A)).



% check whether a variable is not a member of a list
not_member(_, []) :- !.
not_member(X, [H|T]) :- !, X \== H, not_member(X, T).


% A clause becomes true when it contains a literal TrueLit just made true
becomes_true(TrueLit,Clause) :-
    \+ not_member(TrueLit,Clause).

% simplify clauses by removing FalseLit, this is resolution
simplify(FalseLit,Clause,SimplifedClause) :-
    delete_predicate(Clause, FalseLit, SimplifedClause).


% Operator KNF|{Lit}
set_literal(Lit,Clauses,NewClauses) :-
    exclude(becomes_true(Lit),Clauses,Clauses2), % remove all clauses that are now true
    negate(Lit,NegLit),
    maplist(simplify(NegLit),Clauses2,NewClauses). % now simplify all clauses where Lit occurs negatively


unit_propagate([[false]], _, _, _) :- !, fail.
unit_propagate([[true]], Model, Formula, Model) :- !.

unit_propagate(Formula, Model, NewFormula, R) :-
    not(member([], Formula)),
    (
        select([Lit], Formula, Clauses), % there is a unit clause in the list of Clauses
        set_literal(Lit, Clauses, NewClauses),
        append([Lit], Model, NModel),
        unit_propagate(NewClauses, NModel, NewFormula, R)
    ),
    !.

unit_propagate(Formula, [false], _, _) :- !, fail.
unit_propagate(Formula, Model, Formula, Model) :- not(member([], Formula)), !.


choose_literal([],[]).
choose_literal(List, Literal) :-
    nth0(0, List, FList),
    include(non_true_false, FList, Element),
    nth0(0, Element, Literal).

choose_literal(List, Literal) :-
    nth0(0, List, FList),
    include(non_true_false, FList, Element),
    nth0(0, Element, NElement),
    negate(NElement,Literal).
    

% Predicate to check if an element is not true or false
non_true_false(X) :-
    dif(X, true),
    dif(X, false).


dpll([], Model, Model) :- !.


dpll(Formula, Model, RModel) :-
    unit_propagate(Formula, Model, NewFormula, NewModel),
    !,
    append(NewModel, Model, TempM),
    length(NewFormula, L),
    (L == 0 ->  
        dpll([], NewModel, RModel),
        !
    ;
        choose_literal(NewFormula, Literal),
        append([Literal], TempM, NModel),
        set_literal(Literal, NewFormula, Clauses2),
        dpll(Clauses2,NModel, RModel)
    ).

% Reformat input by adding pos/neg to variables
reformat_input([], []).
reformat_input([Clause|Clauses], [ReformattedClause|ReformattedClauses]) :-
    reformat_clause(Clause, ReformattedClause),
    reformat_input(Clauses, ReformattedClauses).

reformat_clause([], []).

reformat_clause([Var|Vars], [Var|ReformattedVars]) :-
    (
        Var==true;
        Var==false
    ),
    reformat_clause(Vars, ReformattedVars),
    !.

reformat_clause([Var|Vars], [pos(Var)|ReformattedVars]) :-
    not(is_negated(Var)),
    !,
    reformat_clause(Vars, ReformattedVars).

reformat_clause([not(Var)|Vars], [neg(Var)|ReformattedVars]) :-
    reformat_clause(Vars, ReformattedVars).


% Helper predicate to check if a variable is negated
is_negated(Term) :-
    compound(Term),            % Check if Term is a compound term
    functor(Term, not, 1),     % Check if Term is of the form not(_)
    arg(1, Term, Var).
    
delete_predicate([], _, []).
delete_predicate([H|T], Predicate, Result) :-
    H \== Predicate,
    !,
    delete_predicate(T, Predicate, Rest),
    Result = [H|Rest].
delete_predicate([H|T], Predicate, T) :- !.  