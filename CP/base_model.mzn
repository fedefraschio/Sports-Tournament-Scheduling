include "globals.mzn";

% ------ Parameters
int: N; %number of teams
int: W = N - 1; %number of weeks
int: P = N div 2; %number of periods

% ------ Decision Variables
array[1..P, 1..W] of var 1..N: Home;
array[1..P, 1..W] of var 1..N: Away;

% ------ Constraint

% Home team and the Away team must be different in every match
constraint forall(w in 1..W, p in 1..P)(Home[p,w] != Away[p,w]);

% Every team plays once a week
constraint forall(w in 1..W)(global_cardinality([Home[p,w] | p in 1..P] ++ [Away[p,w] | p in 1..P], [t | t in 1..N], [1 | t in 1..N]));

% Every team plays at most twice in the same period over the tournament
constraint
forall(p in 1..P) (
  global_cardinality_low_up(
    [Home[p,w] | w in 1..W] ++ [Away[p,w] | w in 1..W],
    [t | t in 1..N],
    [0 | t in 1..N],    
    [2 | t in 1..N]      
  )
);

% Every team plays with every other team only once

constraint
forall(t1, t2 in 1..N where t1 < t2) (
  sum(w in 1..W, p in 1..P)(
    (Home[p,w] = t1 /\ Away[p,w] = t2) \/ (Home[p,w] = t2 /\ Away[p,w] = t1)
  ) = 1
);




%------ Search
solve satisfy; 

