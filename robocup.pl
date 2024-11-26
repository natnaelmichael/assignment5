% Enter the names of your group members below.
% If you only have 2 group members, leave the last space blank
%
%%%%%
%%%%% NAME: Natnael Michael
%%%%% NAME:
%%%%% NAME:
%
% Add the required rules in the corresponding sections. 
% If you put the rules in the wrong sections, you will lose marks.
%
% You may add additional comments as you choose but DO NOT MODIFY the comment lines below
%

%%%%% SECTION: robocup_setup
%%%%%
%%%%% These lines allow you to write statements for a predicate that are not consecutive in your program
%%%%% Doing so enables the specification of an initial state in another file
%%%%% DO NOT MODIFY THE CODE IN THIS SECTION
:- dynamic hasBall/2.
:- dynamic robotLoc/4.
:- dynamic scored/1.

%%%%% This line loads the generic planner code from the file "planner.pl"
%%%%% Just ensure that that the planner.pl file is in the same directory as this one
:- [planner].

%%%%% SECTION: init_robocup
%%%%% Loads the initial state from either robocupInit1.pl or robocupInit2.pl
%%%%% Just leave whichever one uncommented that you want to test on
%%%%% NOTE, you can only uncomment one at a time
%%%%% HINT: You can create other files with other initial states to more easily test individual actions
%%%%%       To do so, just replace the line below with one loading in the file with your initial state
:- [robocupInit1].
%:- [robocupInit2].

%%%%% SECTION: goal_states_robocup
%%%%% Below we define different goal states, each with a different ID
%%%%% HINT: It may be useful to define "easier" goals when starting your program or when debugging
%%%%%       You can do so by adding more goal states below
%%%%% Goal XY should be read as goal Y for problem X

%% Goal states for robocupInit1
goal_state(11, S) :- robotLoc(r1, 0, 1, S).
goal_state(12, S) :- hasBall(r2, S).
goal_state(13, S) :- hasBall(r3, S).
goal_state(14, S) :- scored(S). 
goal_state(15, S) :- robotLoc(r1, 2, 2, S).
goal_state(16, S) :- robotLoc(r1, 3, 2, S).

%% Goal states for robocupInit1
goal_state(21, S) :- scored(S). 
goal_state(22, S) :- robotLoc(r1, 2, 4, S).

%%%%% SECTION: precondition_axioms_robocup
%%%%% Write precondition axioms for all actions in your domain. Recall that to avoid
%%%%% potential problems with negation in Prolog, you should not start bodies of your
%%%%% rules with negated predicates. Make sure that all variables in a predicate 
%%%%% are instantiated by constants before you apply negation to the predicate that 
%%%%% mentions these variables. 


validPosition(Row, Col) :-
    nonvar(Row), nonvar(Col),  % Ensure Row and Col are bound
    numRows(NR), numCols(NC),
    Row > -1, Row < NR,
    Col > -1, Col < NC.

% Adjacent predicate for flexibility
adjacent(Row1, Col1, Row2, Col2) :- 
    ground(Row1), ground(Col1), ground(Row2), ground(Col2),
    (Col1 =:= Col2, abs(Row1 - Row2) =:= 1);
    (Row1 =:= Row2, abs(Col1 - Col2) =:= 1).


clearPath(Row1, Col1, Row2, Col2) :- % Vertical move
    Col1 =:= Col2,
    min(Row1, Row2, MinRow),
    max(Row1, Row2, MaxRow),
    \+ (between(MinRow, MaxRow, R), 
        R \= Row1, R \= Row2, 
        opponentAt(R, Col1)).

clearPath(Row1, Col1, Row2, Col2) :- % Horizontal move
    Row1 =:= Row2,
    min(Col1, Col2, MinCol),
    max(Col1, Col2, MaxCol),
    \+ (between(MinCol, MaxCol, C), 
        C \= Col1, C \= Col2, 
        opponentAt(Row1, C)).

    % Check if path is clear of opponents for passing/shooting
    % Vertical path check
    %(Col1 =:= Col2,
     %MinRow is min(Row1, Row2),
     %MaxRow is max(Row1, Row2),
     %\+ (between(MinRow, MaxRow, R), opponentAt(R, Col1)));
    % Horizontal path check
    %(Row1 =:= Row2,
     %MinCol is min(Col1, Col2),
     %MaxCol is max(Col1, Col2),
     %\+ (between(MinCol, MaxCol, C), opponentAt(Row1, C))).

% Move action preconditions
poss(move(Robot, Row1, Col1, Row2, Col2), S) :-
    robot(Robot),
    validPosition(Row1, Col1),
    validPosition(Row2, Col2),
    robotLoc(Robot, Row1, Col1, S),
    adjacent(Row1, Col1, Row2, Col2),
    clearPath(Row1, Col1, Row2, Col2).

% Pass action preconditions
poss(pass(Robot1, Robot2), S) :-
    robot(Robot1), robot(Robot2),
    Robot1 \= Robot2,
    hasBall(Robot1, S),
    robotLoc(Robot1, Row1, Col1, S),
    robotLoc(Robot2, Row2, Col2, S),
    % Must be in same row or column
    (Row1 =:= Row2),
    % Path must be clear of opponents
    clearPath(Row1, Col1, Row2, Col2).

poss(pass(Robot1, Robot2), S) :-
    robot(Robot1), robot(Robot2),
    Robot1 \= Robot2,
    hasBall(Robot1, S),
    robotLoc(Robot1, Row1, Col1, S),
    robotLoc(Robot2, Row2, Col2, S),
    % Must be in same row or column
    (Col1 =:= Col2),
    % Path must be clear of opponents
    clearPath(Row1, Col1, Row2, Col2).


% Shoot action preconditions
poss(shoot(Robot), S) :-
    robot(Robot),
    hasBall(Robot, S),
    robotLoc(Robot, Row, Col, S),
    goalCol(GoalCol),
    Col =:= GoalCol,
    % Path to goal must be clear of opponents
    clearPath(Row, Col, Row, GoalCol).


%%%%% SECTION: successor_state_axioms_robocup
%%%%% Write successor-state axioms that characterize how the truth value of all 
%%%%% fluents change from the current situation S to the next situation [A | S]. 
%%%%% You will need two types of rules for each fluent: 
%%%%% 	(a) rules that characterize when a fluent becomes true in the next situation 
%%%%%	as a result of the last action, and
%%%%%	(b) rules that characterize when a fluent remains true in the next situation,
%%%%%	unless the most recent action changes it to false.
%%%%% When you write successor state axioms, you can sometimes start bodies of rules 
%%%%% with negation of a predicate, e.g., with negation of equality. This can help 
%%%%% to make them a bit more efficient.
%%%%%
%%%%% Write your successor state rules here: you have to write brief comments %

% Robot Location SSA
robotLoc(Robot, Row, Col, [A|S]) :-
	% Location changes when robot moves there
	(A = move(Robot, _, _, Row, Col));
	% Location persists if robot doesn't move elsewhere
	(robotLoc(Robot, Row, Col, S),
 	\+ (A = move(Robot, Row, Col, _, _))).

% Has Ball SSA
hasBall(Robot, [A|S]) :-
	% Get ball from pass
	(A = pass(_, Robot));
	% Keep ball unless passed or shot
	(hasBall(Robot, S),
\+ (A = pass(Robot, _)),
\+ (A = shoot(Robot))).

% Scored SSA
scored([A|_]) :-
    A = shoot(_).
scored([_|S]) :-
    scored(S).


%%%%% SECTION: declarative_heuristics_robocup
%%%%% The predicate useless(A,ListOfPastActions) is true if an action A is useless
%%%%% given the list of previously performed actions. The predicate useless(A,ListOfPastActions)
%%%%% helps to solve the planning problem by providing declarative heuristics to 
%%%%% the planner. If this predicate is correctly defined using a few rules, then it 
%%%%% helps to speed-up the search that your program is doing to find a list of actions
%%%%% that solves a planning problem. Write as many rules that define this predicate
%%%%% as you can: think about useless repetitions you would like to avoid, and about 
%%%%% order of execution (i.e., use common sense properties of the application domain). 
%%%%% Your rules have to be general enough to be applicable to any problem in your domain,
%%%%% in other words, they have to help in solving a planning problem for any instance
%%%%% (i.e., any initial and goal states).
%%%%%	
%%%%% write your rules implementing the predicate  useless(Action,History) here. %

% 1. Don't move back and forth between same locations
useless(move(Robot, Row2, Col2, Row1, Col1), [move(Robot, Row1, Col1, Row2, Col2)|_]) :- !.

% 2. Don't pass ball back and forth between same robots
useless(pass(Robot2, Robot1), [pass(Robot1, Robot2)|_]) :- !.

% 3. Don't move a robot that just received a pass (let them shoot or pass first)
useless(move(Robot, _, _, _, _), [pass(_, Robot)|_]) :- !.

% 4. Don't pass to a robot that can't shoot or pass further (blocked by opponents)
useless(pass(_, Robot2), _) :-
    robotLoc(Robot2, Row2, Col2, _),
    goalCol(GoalCol),
    Col2 =:= GoalCol,
    \+ clearPath(Row2, Col2, Row2, GoalCol).

% 5. Don't move away from goal column if you have the ball and clear shot
useless(move(Robot, Row1, Col1, _, Col2), S) :-
    hasBall(Robot, S),
    goalCol(GoalCol),
    Col1 =:= GoalCol,
    Col2 \= GoalCol,
    clearPath(Row1, Col1, Row1, GoalCol).

