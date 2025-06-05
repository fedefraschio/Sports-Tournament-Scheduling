include "globals.mzn";

% ------ Parameters
int: N; %number of teams
int: W = N-1; %number of weeks
int: P = N div 2; %number of periods

% ------ Decision variables
% Schedule[1,1] = 2 means "team 1 plays in week 1 vs. team 2"
% Schedule[2,1] = 1 means "team 2 plays in week 1 vs. team 1"
% Period[1,1] = 3 means "team 1 plays in week 1 in period 3"
% Period[2,1] = 3 means "team 2 plays in week 1 in period 3"
array[1..N, 1..W] of var 1..N: Schedule;
array[1..N, 1..W] of var 1..P: Period; 


% ------ Constraint

% In each week, every team is assigned to a game against another team
% Match assignment is symmetric: if team i plays vs. team j, then team j plays vs. team i
constraint forall(w in 1..W)(
  symmetric_all_different([Schedule[t,w] | t in 1..N])
);

% NO LONGER USEFULL, It is replaced by the global_cardinality constraint that also checks that a team does not play against itself
%constraint forall(t in 1..N)
  %(all_different([Schedule[t,w] | w in 1..W])
%);

% Every team plays with every other team only once (a team does not play against itself)
constraint forall(t in 1..N)(
  global_cardinality([Schedule[t,w]| w in 1..W], [a | a in 1..N where t != a], [1 | w in 1..W])
);

% In every week, each period is assigned exactly one game
% which means that each period is assigned exactly two teams
constraint forall(w in 1..W) (
  global_cardinality([Period[t, w] | t in 1..N], [p | p in 1..P], [2 | p in 1..P])
);

% Two teams matched to play against each other in a given week
% must be assigned to the same period, since they share the same game
constraint forall(w in 1..W)(
  forall(i, j in 1..N where i < j)(
    (Schedule[i,w] == j /\ Schedule[j,w] == i) -> Period[i,w] == Period[j, w])
);

% Every team plays at most twice in the same period over the tournament
constraint forall(t in 1..N) (
  global_cardinality_low_up([Period[t, w] | w in 1..W], [p | p in 1..P], [0 | p in 1..P], [2 | p in 1..P])
);
  
 
% ------ Search
solve satisfy; 


