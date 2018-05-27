from collections import defaultdict
from queue import Queue

import matplotlib.pyplot as plt
import numpy as np
import os

import pickle
import time

from random import shuffle
from itertools import combinations
from scipy.special import comb

switch_literal = lambda x: x[1:] if x.startswith('-') else '-'+x
deepcopy = lambda x: pickle.loads(pickle.dumps(x))

def parse_input(input_file):
    
    """
    literal_clauseNum: {Literal: Set of clause numbers that are still in consideration for this variable}                        
    
    clauseNum_clause: {Clause number: Set of literals that could still satisfy this clause}
    
    literal_boolen: {Literal: boolean on whether literal set of True/False/None, None meaning could be either, doesn't matter}
    
    input_file:
    c DIMACS CNF: conjunction/AND of one or more clauses, where a clause is a disjunction/OR of literals
    c Comments start with a c, First lines begins with p and describes the probelm and all clause lines end with a 0
    c Can't have same variable in both forms in same clause. So A ~A is not allowed. Can have them in separate clauses.
                        
    """

    all_clauses = []  # List of all clauses that appear in input. Used for SAT checking the mapping given by DPLL

    literal_clauseNum = defaultdict(set)

    def filler():
        return None

    literal_boolen = defaultdict(filler)

    clauseNum_clause = {}

    clause_counter = 0

    with open(input_file, 'r') as fin:
        for line in fin:
            line = line.strip()
            # Do checks on comments
            if line.startswith('c') or line.startswith('p') or line.startswith('0') or line.startswith('%'):
                continue
            if len(line) > 0:
                clause = []
                clause_counter += 1
                for literal in line.split():
                    if literal == '0':
                        # End of line, ignore in DIMACS CNF format
                        continue
                    clause.append(literal)
                    literal_clauseNum[literal].add(clause_counter)
                clauseNum_clause[clause_counter] = set(clause)
                all_clauses.append(clause)

    return literal_clauseNum, clauseNum_clause, literal_boolen, all_clauses

def unit_prop(literal_clauseNum, clauseNum_clause, literal_boolen):
    keep_updating = True
    while keep_updating:
        keep_updating = False # Assuming we've found all unit clauses
        for clauseNum in list(clauseNum_clause.keys()):
            if clauseNum not in clauseNum_clause:
                continue
            clause = clauseNum_clause[clauseNum]
            # Clause contains the remaining literals that could potentially satisfy this clause. 
            if len(clause) == 0:
                # Empty clause, so need to return True for empty clause detected
                return True, None, None, None
            if len(clause) > 1:
                # Can't do unit prop 
                continue

            literal = clause.pop()  # Needs to be set to True
            clause.add(literal)  # Removed later
            literal_boolen[literal] = True
            keep_updating = True  # Since we found one unit clause, maybe more

    #         print(literal)
    #         print(literal_clauseNum)
    #         print(clauseNum_clause)

            # For all clauses that have this literal, they have been satisfied now
            # 1) Gather all pairs of (literals, clauseNum) that appear in these clauses so we can remove them from literal_clauseNum
            # 2) Delete these clauses from clauseNum_clause
            pairs_to_delete = []
            for clauseNums_with_literal in literal_clauseNum[literal]:
                for literals_in_clauseNums in clauseNum_clause[clauseNums_with_literal]:
                    pairs_to_delete.append((literals_in_clauseNums, clauseNums_with_literal))

    #         print(pairs_to_delete)

            for literals_in_clauseNums, clauseNums_with_literal in pairs_to_delete:
                literal_clauseNum[literals_in_clauseNums].discard(clauseNums_with_literal)
                if clauseNums_with_literal in clauseNum_clause:
                    del clauseNum_clause[clauseNums_with_literal]

            # For all the clauses with opposite literal, remove the literal from the clause
            if switch_literal(literal) not in literal_clauseNum: # if the opposite variable doesn't exist, skip
                continue

            opposite_literal = switch_literal(literal)
            literal_boolen[opposite_literal] = False

            for clauseNums_with_literal in literal_clauseNum[opposite_literal]:
                clauseNum_clause[clauseNums_with_literal].discard(opposite_literal)

            literal_clauseNum[opposite_literal] = set()  # It is not watching any clauses anymore

    #         print("OPPO")
    #         print(literal_clauseNum)
    #         print(clauseNum_clause)
        
    return False, literal_clauseNum, clauseNum_clause, literal_boolen


def pure_literal(literal_clauseNum, clauseNum_clause, literal_boolen):
    keep_updating = True
    while keep_updating:
        keep_updating = False
        for literal in list(literal_clauseNum.keys()):
            if literal in literal_boolen:
                continue

            opposite_literal = switch_literal(literal)
            if opposite_literal not in literal_boolen: # The opposite variable has not been assigned yet
                # If it doesn't exist or it does but it doesn't have to satisfy any clauses
                if opposite_literal not in literal_clauseNum or len(literal_clauseNum[opposite_literal]) == 0:
                    # LITERAL IS A PURE LITERAL
                    keep_updating = True
                    literal_boolen[literal] = True

                    # All the clauses that literal exists in has been made true, so remove the clauses and make literal watch no clause
                    pairs_to_delete = []
                    for clauseNums_with_literal in literal_clauseNum[literal]:
                        for literals_in_clauseNums in clauseNum_clause[clauseNums_with_literal]:
                            pairs_to_delete.append((literals_in_clauseNums, clauseNums_with_literal))

            #         print(pairs_to_delete)

                    for literals_in_clauseNums, clauseNums_with_literal in pairs_to_delete:
                        literal_clauseNum[literals_in_clauseNums].discard(clauseNums_with_literal)
                        if clauseNums_with_literal in clauseNum_clause:
                            del clauseNum_clause[clauseNums_with_literal]
                        
    return literal_clauseNum, clauseNum_clause, literal_boolen

def bohm(literal_clauseNum, clauseNum_clause):
    """
    See Heuristics folder. Lexicographic order of the vector (H1(x), H2(x), ..., Hn(x)) means we first choose highest H1(x)
    variable. When tied we then choose amongst tied variable highest H2 variable. When tied then H3 and so on.
    
    We've had to manage edge cases here but don't mention that in report. Only give formula from paper
    """
    pos_literal_count = defaultdict(lambda: [0, 0, 0])  # This default initialisation only works for 3 SAT
    neg_literal_count = defaultdict(lambda: [0, 0, 0])
    
    for literal, clauseNums in literal_clauseNum.items():
        if literal.startswith('-'):
            for clauseNum in clauseNums:
                clause = clauseNum_clause[clauseNum]
                neg_literal_count[literal][len(clause)-1] += 1
        else:
            for clauseNum in clauseNums:
                clause = clauseNum_clause[clauseNum]
                pos_literal_count[literal][len(clause)-1] += 1
                
    final_count = []
    # Sometimes we only have negative literals left. So then we just use those
    for literal, pos_counts in (pos_literal_count.items() or neg_literal_count.items()):
        other_literal = switch_literal(literal)
        
        if literal.startswith('-'):
            # pos_literal_counts is empty. So literal and pos_counts actually are neg_literal_counts
            neg_counts = pos_literal_count[other_literal]
        else:
            # pos_literal_counts isn't empty. So continue as normal
            neg_counts = neg_literal_count[other_literal]
        
        final_count.append(([max(p, n) + 2 * min(p, n) for p, n in zip(pos_counts, neg_counts)], literal))
            
    final_count.sort(reverse=True)
    score_vector, literal = final_count[0]
    other_literal = switch_literal(literal)
    
    if literal.startswith('-'):
        neg_literal = literal
        pos_literal = other_literal
    else:
        neg_literal = other_literal
        pos_literal = literal
    
    # Since the score for positive and negative literal is the same, choose one which the highest overall score
    if sum(pos_literal_count[pos_literal]) >= sum(neg_literal_count[neg_literal]):
        literal = pos_literal
    else:
        literal = neg_literal
    
    return literal, score_vector


def set_var(literal, boolean, literal_clauseNum, clauseNum_clause, literal_boolen):
    literal_boolen[literal] = boolean

    if boolean == False:
        literal = switch_literal(literal)
        literal_boolen[literal] = True
    
    # Unit-prop logic below
    pairs_to_delete = []
    for clauseNums_with_literal in literal_clauseNum[literal]:
        for literals_in_clauseNums in clauseNum_clause[clauseNums_with_literal]:
            pairs_to_delete.append((literals_in_clauseNums, clauseNums_with_literal))

    #         print(pairs_to_delete)

    for literals_in_clauseNums, clauseNums_with_literal in pairs_to_delete:
        literal_clauseNum[literals_in_clauseNums].discard(clauseNums_with_literal)
        if clauseNums_with_literal in clauseNum_clause:
            del clauseNum_clause[clauseNums_with_literal]

    # For all the clauses with opposite literal, remove the literal from the clause
    if switch_literal(literal) not in literal_clauseNum: # if the opposite variable doesn't exist, skip
        return literal_clauseNum, clauseNum_clause, literal_boolen

    opposite_literal = switch_literal(literal)
    literal_boolen[opposite_literal] = False

    for clauseNums_with_literal in literal_clauseNum[opposite_literal]:
        clauseNum_clause[clauseNums_with_literal].discard(opposite_literal)

    literal_clauseNum[opposite_literal] = set()  # It is not watching any clauses anymore

    #         print("OPPO")
    #         print(literal_clauseNum)
    #         print(clauseNum_clause)
    
    return literal_clauseNum, clauseNum_clause, literal_boolen




# Methods that are used by the Env class to get state features

def number_of_clauses(literal_clauseNum):
    """ Returns the number of clauses each of the literal is present in """
    ans = np.zeros(actions)
    for literal, clauseNums in literal_clauseNum.items():
        ans[LIT_IDX[literal]] = len(clauseNums)
    return ans


def number_of_horn_clauses(clauseNum_clause):
    """ Returns the number of horn clauses each literal is present in """
    ans = np.zeros(actions)
    for clause in clauseNum_clause.values():
        if len(clause) == 0:
            continue
        pos_literals = list(filter(lambda x: not x.startswith('-'), clause))
        if len(pos_literals) == 1:
            ans[LIT_IDX[pos_literals[0]]] += 1
            
    return ans
        
def pos_neg_ratio(literal_clauseNum):
    ans = np.zeros(actions)
    
    for literal, clauseNums in literal_clauseNum.items():
        opposite_literal = switch_literal(literal)
        if opposite_literal in literal_clauseNum and len(literal_clauseNum[opposite_literal]) > 0:
            ratio = len(clauseNums) / len(literal_clauseNum[opposite_literal])
        else:
            ratio = len(clauseNums)
            
        ans[LIT_IDX[literal]] = ratio
        
    return ans

def CVIG(literal_clauseNum, clauseNum_clause):
    """
    Caluse-variable incidence graph. We create a bipartite graph (a matrix) with literals in rows and clauses in columns.
    See Features_2 PDF file.
    """
    
    clauseNum_index_mapping = {}
    
    for i, clauseNum in enumerate(clauseNum_clause):
        clauseNum_index_mapping[clauseNum] = i
        
    if len(clauseNum_clause) == 0:
        return np.zeros((len(LIT_IDX), 1))
    
    graph = np.zeros((len(LIT_IDX), len(clauseNum_index_mapping)))
    for literal, clauseNums in literal_clauseNum.items():
        for clauseNum in clauseNums:
            graph[LIT_IDX[literal]] [clauseNum_index_mapping[clauseNum]] = 1/len(clauseNums)
    
    return graph


def VIG(literal_clauseNum, clauseNum_clause):
    """
    Variable incidence graph.
    """
    if len(clauseNum_clause) == 0:
        return np.zeros((actions, actions))
    
    graph = np.zeros((actions, actions))
    
    for clause in clauseNum_clause.values():
        if len(clause) < 2:
            continue
        for x, y in combinations(clause, 2):
            w = 1 / (comb(len(clause), 2))  # Try combinations with replacement to add self-loops
            graph[LIT_IDX[x]][LIT_IDX[y]] = w
            graph[LIT_IDX[y]][LIT_IDX[x]] = w
            
    return graph

class Env:
    
    def __init__(self, input_file):
        self.input_file = input_file
        self.stack = [] # We use a stack to hold the next states to explore. i.e. we do DFS as less memory requirements than BFS
        self.state = None
    
    def reset(self):
        # Returns state
        literal_clauseNum, clauseNum_clause, literal_boolen, _ = parse_input(self.input_file)
        self.state = (literal_clauseNum, clauseNum_clause, literal_boolen)
        return self.get_state()
    
    def get_state(self):
        literal_clauseNum, clauseNum_clause, literal_boolen = self.state
        
        num_clauses = number_of_clauses(literal_clauseNum)
        num_horn_clauses = number_of_horn_clauses(clauseNum_clause)
        
        pn_ratio = pos_neg_ratio(literal_clauseNum)
        
        vig_graph = VIG(literal_clauseNum, clauseNum_clause)
        vig_mean, vig_var = np.mean(vig_graph, axis=0), np.var(vig_graph, axis=0)
        
        cvig_graph = CVIG(literal_clauseNum, clauseNum_clause)
        cvig_mean, cvig_var = np.mean(cvig_graph, axis=1), np.var(cvig_graph, axis=1)
        
        state_matrix = list(zip(num_clauses, num_horn_clauses, pn_ratio, vig_var, cvig_mean, cvig_var))
#         state_matrix = list(zip(num_clauses, num_horn_clauses, cvig_mean, cvig_var))
#         state_matrix = list(zip(num_clauses, num_horn_clauses))
        return np.array(state_matrix)  # Returns a 2D array of the state matrix
    
        
    def step(self, action):
        """
        Returns: next_state_1, next_state_2, reward, done
        reward = 0 if reached a leaf node, 0 if not
        """
        literal_clauseNum, clauseNum_clause, literal_boolen = self.state
        
        num_clauses_start = 0
        for clause in clauseNum_clause.values():
            if len(clause) > 0:
                num_clauses_start += 1
            else:
                # This is reached when we reached an UNSAT state in previous step and popped off another UNSAT from the stack
                isEmpty = len(self.stack) == 0
                if not isEmpty:
                    self.state = self.stack.pop()
                return None, -1, isEmpty
        
        literal = action
        
        # Set the chosen literal to be True
        literal_clauseNum_T, clauseNum_clause_T, literal_boolen_T = \
            set_var(literal, True, deepcopy(literal_clauseNum), deepcopy(clauseNum_clause), dict(literal_boolen))
            
            
        # Set new state
        self.state = (literal_clauseNum_T, clauseNum_clause_T, literal_boolen_T)
        
        # Set the chosen literal to be False
        literal_clauseNum_F, clauseNum_clause_F, literal_boolen_F = \
            set_var(literal, False, literal_clauseNum, clauseNum_clause, literal_boolen)
            
        # Check that setting chosen to False hasn't made any empty clauses
        valid = True
        for clause in clauseNum_clause_F.values():
            if len(clause) == 0:
                valid = False
        
        # Add new state to stack
        if valid:
            self.stack.append((literal_clauseNum_F, clauseNum_clause_F, literal_boolen_F))
        
        
        if clauseNum_clause_T == {} or clauseNum_clause_F == {}:  # We have satisfied
#             print("INITIAL")
            return None, 1, True
        
        
        literal_clauseNum, clauseNum_clause, literal_boolen = self.state
        
        # Do unit prop
        empty_clause, literal_clauseNum, clauseNum_clause, literal_boolen = \
            unit_prop(literal_clauseNum, clauseNum_clause, literal_boolen)
            
        if empty_clause:
            isEmpty = len(self.stack) == 0
            if not isEmpty:
                self.state = self.stack.pop()
            return None, -1, isEmpty
        
        if clauseNum_clause == {}:
#             print("UNIT PROP")
            return None, 1, True
        
        # Do pure literal elimination
        literal_clauseNum, clauseNum_clause, literal_boolen = \
            pure_literal(literal_clauseNum, clauseNum_clause, literal_boolen)
            
            
        if clauseNum_clause == {}:
#             print("PLE")
            return None, 1, True
        
        num_clauses_end = 0
        for clause in clauseNum_clause.values():
            if len(clause) > 0:
                num_clauses_end += 1
        
        if num_clauses_start > 0:
            fraction_of_clauses_removed = (num_clauses_start - num_clauses_end)/num_clauses_start
        else:
            fraction_of_clauses_removed = 0
        
        self.state = (literal_clauseNum, clauseNum_clause, literal_boolen)
                
        return None, -1 + fraction_of_clauses_removed, False


def DQN_make_epsilon_greedy_policy(estimator, epsilon, nA):
    """
    Creates an epsilon-greedy policy based on a given Q-function approximator and epsilon.

    Args:
        estimator: An estimator that returns q values for a given state
        nA: Number of actions in the environment.

    Returns:
        A function that takes the (sess, observation, epsilon) as an argument and returns
        the probabilities for each action in the form of a numpy array of length nA.

    """
    def policy_fn(observation, literal_clauseNum):
        A = np.ones(nA, dtype=float) * epsilon / nA
        q_values = estimator.predict(observation)
        
        # Make q_values of unusable actions -inf
        for literal, clauseNums in literal_clauseNum.items():
            if len(clauseNums) == 0:
                idx = LIT_IDX[literal]
                q_values[idx] = -np.inf
        
        best_action = np.argmax(q_values)
        A[best_action] += (1.0 - epsilon)
        return A
    return policy_fn


def redistribute_probability(action_prob, literal_clauseNum):
    total_gained = 0
    idx_to_increase = []
    
    for literal in LIT_IDX:  # If a literal doesn't appear in the formula, then literal_clauseNum won't have it
        clauseNums = literal_clauseNum[literal]
        if len(clauseNums) == 0:
            idx = LIT_IDX[literal]
            total_gained += action_prob[idx]
            action_prob[idx] = 0
        else:
            idx_to_increase.append(LIT_IDX[literal])
            
    per_idx_inc = total_gained / len(idx_to_increase)
    
    for idx in idx_to_increase:
        action_prob[idx] += per_idx_inc
    return action_prob

def copy_params(copy_from_est, copy_to_est):
    copy_to_est.model.set_weights(copy_from_est.model.get_weights())
    
    
    
def test(test_files, ϵ=1.0, estimator=None, num_top_actions=3, use_hybrid=False):

    total_reward, total_length, total_states, total_actions = 0, 0, [], []
    
    if estimator is None:
        estimator = Estimator()  # Never used if epsilon > 1
        
    policy = DQN_make_epsilon_greedy_policy(estimator, ϵ, actions)
    
    for i, filepath in enumerate(test_files):
        
#         if i % 100 == 0:
#             print("Testing file", i)
        
        env = Env(filepath)
        state = env.reset()
        
        while True:
            literal_clauseNum, clauseNum_clause, _ = env.state
            
            action_prob = policy(state, literal_clauseNum)
            action_prob = redistribute_probability(action_prob, literal_clauseNum)
            
            if use_hybrid:
                # Using Hybrid approach for testing
                top_action_idx = np.random.choice(np.arange(len(action_prob)), p=action_prob, size=num_top_actions)
                action_literal_clauseNum = {IDX_LIT[idx]: literal_clauseNum[IDX_LIT[idx]] for idx in top_action_idx}
                action, _ = bohm(action_literal_clauseNum, clauseNum_clause)
                action_idx = LIT_IDX[action]
            else:
                # Only relying on policy
                action_idx = np.random.choice(np.arange(len(action_prob)), p=action_prob)
                action = IDX_LIT[action_idx]
                

            _, reward, done = env.step(action)

            # Stats
            total_length += 1
            total_reward += reward
            total_actions.append(action_idx)

            if done:
                break

            state = env.get_state()

    return total_reward/len(test_files), total_length/len(test_files), np.array(total_actions) #, total_states


from sklearn.linear_model import SGDRegressor
from sklearn.preprocessing import StandardScaler

class Estimator():
    
    def __init__(self):
        # We create a separate model for each action in the environment's
        # action space. Alternatively we could somehow encode the action
        # into the features, but this way it's easier to code up.
        self.model = SGDRegressor(learning_rate="constant", eta0=0.001, penalty='l2')
        self.model.partial_fit([self.featurize_state(np.zeros(state_space))], [0])
        self.scaler = StandardScaler()
        self.scaler.fit([self.featurize_state(np.zeros(state_space))], [np.zeros(state_space)])
    
    def featurize_state(self, state):
        # Needs to return a 1D array
        return np.array(state)
    
    def predict(self, state):
        preds = self.model.predict(state).squeeze()
        return preds
        
    def update(self, state, action_idx, reward):
        model = self.model
        state_feature = self.featurize_state(state[action_idx])
        
        if len(state_feature.shape) < 2:
            state_feature = np.expand_dims(state_feature, 0)
        
        self.scaler.partial_fit(state_feature)
        state_feature = self.scaler.transform(state_feature) # Returns a 2D array
        model.partial_fit(state_feature, [reward])
        
        return 0
    
    

def train(training_files, epsilon=0.4, epsilon_decay=0.94, discount_factor=1.0, num_top_actions=3, output_stats_every=1000):
    total_reward, total_length = [], []
    
    estimator = Estimator()
    
    curr_length = 0
    curr_reward = 0
    
    for j, filepath in enumerate(training_files):
        """ Each file in one episode """
        
        if j % output_stats_every == 0:
            part = j // output_stats_every
            epsilon_decay_j = epsilon_decay**part
            total_reward.append(curr_reward / output_stats_every)
            total_length.append(curr_length / output_stats_every)
            # print(part, total_reward[-1], total_length[-1])

            curr_length = 0
            curr_reward = 0
            policy = DQN_make_epsilon_greedy_policy(estimator, epsilon*epsilon_decay_j, actions)

        env = Env(filepath)
        state = env.reset()

        while True:
            literal_clauseNum, clauseNum_clause, _ = env.state
            
            action_prob = policy(state, literal_clauseNum)
            action_prob = redistribute_probability(action_prob, literal_clauseNum)
            
            # Use below for hybrid approach of training with Heuristic
#             top_action_idx = np.random.choice(np.arange(len(action_prob)), p=action_prob, size=num_top_actions)
#             action_literal_clauseNum = {IDX_LIT[idx]: literal_clauseNum[IDX_LIT[idx]] for idx in top_action_idx}
#             action, _ = bohm(action_literal_clauseNum, clauseNum_clause)
#             action_idx = LIT_IDX[action]
            
            action_idx = np.random.choice(np.arange(len(action_prob)), p=action_prob)
            action = IDX_LIT[action_idx]
            
            _, reward, done = env.step(action)

            # Stats
            curr_length += 1
            curr_reward += reward

            if done:
                td_target = reward
                estimator.update(state, action_idx, td_target)
                break

            next_state = env.get_state()

            q_values = estimator.predict(next_state)
            
            td_target = reward + discount_factor * np.max(q_values)
            current_value = estimator.predict(state)[action_idx]
            td_error = td_target - current_value

            alpha = 0.8
            update_target = current_value + alpha*td_error
            estimator.update(state, action_idx, update_target)

            state = next_state

    total_reward.append(curr_reward / output_stats_every)
    total_length.append(curr_length / output_stats_every)
    # print("Last output:", total_reward[-1], total_length[-1])
    
    return total_reward, total_length, [], estimator
    
        
if __name__ == '__main__':
    use_poly = False
    poly_degree = 7

    numVars = 20
    LITERALS = list(range(-numVars, 0))
    pos_lit = list(range(1, numVars+1))
    LITERALS.extend(pos_lit)
    LIT_IDX = {}  # Global mapping between literal and its position in the action space
    IDX_LIT = {}  # Global mapping between its position in the action space and literal

    for index, var in enumerate(LITERALS):
        LIT_IDX[str(var)] = index
        IDX_LIT[index] = str(var)

    actions = len(LITERALS)  # Number of actions available to use by the agent
    state_space = 6          # Number of metrics for each literal

    directory = '../Tests/CNFGEN_20/'  # RLSAT problems are very simple. SATLIB probelms give more interesting Q-values.
    files = list(map(lambda x: os.path.join(directory, x), os.listdir(directory)))

    split = int(len(files) * 0.6)
    training_files = files[:split]
    shuffle(training_files)

    test_files = files[60000:61000]
    
    ######### ADDING EXTRA TRAINING FILES ##########
    # training_files.append(files[61000:])

#     print("Number of training files:", len(training_files))
#     print("Number of test files:", len(test_files))

    print("TESTING LINEAR NEW ACTION SPACE")

    s = time.time()
    episode_reward_train, episode_length_train, losses, estimator = train(training_files, epsilon=0.8, epsilon_decay=0.94)
    e = time.time()
    print("Done training in", (round(e-s, 2)), "s")
    print()

    print("Starting Testing Hybrid of learnt policy")
    s = time.time()
    episode_reward_test_T, episode_length_test_T, episode_actions_T = test(test_files, ϵ=0, estimator=estimator)
    e = time.time()
    print("Done testing in", (round(e-s, 2)), "s")
    print(episode_reward_test_T, episode_length_test_T)
    print(np.bincount(episode_actions_T))
    print()

    print("Starting Testing Hybrid of random policy")
    s = time.time()
    episode_reward_rand_T, episode_length_rand_T, episode_actions_rand_T = test(test_files)
    e = time.time()
    print("Done testing random policy in ", (round(e-s, 2)), "s")
    print(episode_reward_rand_T, episode_length_rand_T)
    print(np.bincount(episode_actions_rand_T))
    print()

    
    with open('MultipleRunsMetrics/newActionLinear3.pickle', 'wb') as fout:
        pickle.dump((episode_reward_train, episode_length_train), fout)
    
#     with open('CNFGEN_20_50epochs_Hybrid_Linear.pickle', 'wb') as fout:
#         pickle.dump((episode_reward_train, episode_length_train, estimator, episode_reward_test_T, episode_length_test_T, episode_actions_T, episode_reward_test_F, episode_length_test_F, episode_actions_F, episode_reward_rand_T, episode_length_rand_T, episode_actions_rand_T, episode_reward_rand_F, episode_length_rand_F, episode_actions_rand_F), fout)