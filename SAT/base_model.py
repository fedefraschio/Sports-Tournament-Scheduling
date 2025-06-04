#!/usr/bin/env python
# coding: utf-8

# In[1]:


#get_ipython().system('pip3 install z3-solver')


# In[2]:


from itertools import combinations
from z3 import *


# In[3]:


def at_least_one(bool_vars):
  return Or(bool_vars)

def at_most_one(bool_vars):
  return [Not(And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)]

def exactly_one(bool_vars):
  return at_most_one(bool_vars) + [at_least_one(bool_vars)]

def at_most_k(bool_vars, k):
  return And([Or([Not(x) for x in X]) for X in combinations(bool_vars, k+1)])


# In[4]:


def at_least_one_seq(bool_vars):
  return at_least_one(bool_vars)

def at_most_one_seq(bool_vars, name = ""):
  constraints = []
  n = len(bool_vars)
  s = [Bool(f"s_{name}_{i}") for i in range(n-1)]
  constraints.append(Or(Not(bool_vars[0]), s[0]))
  constraints.append(Or(Not(bool_vars[n-1]), Not(s[n-2])))

  for i in range(1, n-1):
    constraints.append(Or(Not(bool_vars[i]), s[i]))
    constraints.append(Or(Not(bool_vars[i]), Not(s[i-1])))
    constraints.append(Or(Not(s[i-1]), s[i]))
  return And(constraints)


def exactly_one_seq(bool_vars, name = ""):
  return And(at_least_one_seq(bool_vars), at_most_one_seq(bool_vars, name))


# In[5]:


def toBinary(num, length = None):
  num_bin = bin(num).split('b')[-1]
  if length:
    return '0'*(length - len(num_bin)) + num_bin
  return num_bin

def at_least_one_bw(bool_vars):
  return at_least_one(bool_vars)

def at_most_one_bw(bool_vars, name = ""):
  constraints = []
  n = len(bool_vars)
  #print(f"n: {n}")
  m = math.ceil(math.log2(n))
  #print(f"m: {m}")
  # additional variables r
  r = [Bool(f"r_{name}_{i}") for i in range(m)]
  #print(f"r : {r}")
  binary_representations = [toBinary(i,m) for i in range(n)]
  #print(f"bin_rep: {binary_representations}")

  for i in range(n):
    for j in range(m):
      phi = Not(r[j])
      if binary_representations[i][j] == '1':
        phi = r[j]
      constraints.append(Or(Not(bool_vars[i]), phi))
  return And(constraints)


def exactly_one_bw(bool_vars, name = ""):
  return And(at_least_one_bw(bool_vars), at_most_one_bw(bool_vars, name))


# In[6]:


def at_most_k_seq(bool_vars, k, name):
    constraints = []
    n = len(bool_vars)
    s = [[Bool(f"s_{name}_{i}_{j}") for j in range(k)] for i in range(n - 1)]
    constraints.append(Or(Not(bool_vars[0]), s[0][0]))
    constraints += [Not(s[0][j]) for j in range(1, k)]
    for i in range(1, n-1):
        constraints.append(Or(Not(bool_vars[i]), s[i][0]))
        constraints.append(Or(Not(s[i-1][0]), s[i][0]))
        constraints.append(Or(Not(bool_vars[i]), Not(s[i-1][k-1])))
        for j in range(1, k):
            constraints.append(Or(Not(bool_vars[i]), Not(s[i-1][j-1]), s[i][j]))
            constraints.append(Or(Not(s[i-1][j]), s[i][j]))
    constraints.append(Or(Not(bool_vars[n-1]), Not(s[n-2][k-1])))
    return And(constraints)




# In[14]:


# Base model without simmetry breaking constraint
def sports_tournament_scheduling(n):
  game = list(combinations(list(range(n)), 2))
  num_game =len(game)
  num_week = n - 1
  num_period = n // 2

  ### Boolean variables
  S = [[[Bool(f"s_{w}_{p}_{g}") for g in range(num_game)] for p in range(num_period)] for w in range(num_week)]
  # S[g][w][p] = True <-> la partita game[g] = (i, j) è programmata nella settimana w, periodo p

  H = [Bool(f"h_{g}") for g in range(num_game)]
  # H[g] = True <-> la partita game[g] = (i,j) è giocata in casa di i, H[g] = False <-> la partita è giocata in casa di j

  s = Solver()

  ### CONSTRAINT every team plays with every other team only once
  for g in range(num_game):
    s.add(exactly_one_bw([S[w][p][g] for w in range(num_week) for p in range(num_period)], name=f'g_{g}'))

  ### CONSTRAINT In each period of every week it is played exactly one game
  for w in range(num_week):
    for p in range(num_period):
      s.add(exactly_one_bw(S[w][p], name=f'w_{w}_p_{p}'))

  ### CONSTRAINT every team plays once a week
  for w in range(num_week):
    for t in range(n):
      game_team_per_week = [S[w][p][g] for p in range(num_period) for g in range(num_game) if t in game[g]]
      s.add(exactly_one_bw(game_team_per_week, name=f'w_{w}_t_{t}'))

  ### CONSTRAINT every team plays at most twice in the same period over the tournament
  for p in range(num_period):
    for t in range(n):
      game_team_per_period = [S[w][p][g] for w in range(num_week) for g in range(num_game) if t in game[g]]
      s.add(at_most_k_seq(game_team_per_period, 2, name=f'p_{p}_t_{t}'))


  if s.check() == sat:
    #model = s.model()
    print("SAT")
  else:
    print('No solutions')



# In[13]:


sports_tournament_scheduling(6)

