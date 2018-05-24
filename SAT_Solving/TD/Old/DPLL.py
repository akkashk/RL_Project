class Env:
    
    def __init__(self, input_file):
        self.input_file = input_file
        self.stack = [] # We use a stack to hold the next states to explore. i.e. we do DFS as less memory requirements than BFS
        self.state = None
        self.actions = {0: 'maxo', 1: 'moms', 2: 'mams', 3: 'jw', 4: 'jw_2', 5: 'bohm'}
        self.action_penalty = {0: 0, 1: 0, 2: 0, 3: 0, 4: -0.1, 5: -0.1}  # Penalty to give each action
    
    def reset(self):
        # Returns state
        literal_clauseNum, clauseNum_clause, literal_boolen, _ = parse_input(self.input_file)
        self.state = (literal_clauseNum, clauseNum_clause, literal_boolen)
        return self.get_state()
    
    def get_state(self):
        literal_clauseNum, clauseNum_clause, literal_boolen = self.state
        
        num_var = number_of_variables(literal_clauseNum)
#         horn_clause = horn_clause_ratio(clauseNum_clause)

#         var_horn_counts = horn_clause_count(literal_clauseNum, clauseNum_clause)
#         var_horn_mean, var_horn_var = np.mean(var_horn_counts), np.var(var_horn_counts)  # DON'T USE
        
#         pn_ratio = pos_neg_ratio(literal_clauseNum)
#         c_v_ratio = clause_to_variable_ratio(literal_clauseNum)
        
#         cvig_graph = CVIG(literal_clauseNum, clauseNum_clause)
#         cvig_mean, cvig_var = np.mean(cvig_graph), np.var(cvig_graph)  # axis=0 gives more different results if we want this to return vector
        
#         vig_graph = VIG(literal_clauseNum, clauseNum_clause)
#         vig_mean, vig_var = np.mean(vig_graph), np.var(vig_graph)
        
#         return [num_var, c_v_ratio, cvig_mean, cvig_var]
#         return [num_var, horn_clause, var_horn_mean, var_horn_var, pn_ratio, c_v_ratio, cvig_mean, cvig_var, vig_mean, vig_var]
        return num_var
    
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
                
        if num_clauses_start > 0:
            fraction_of_clauses_removed = num_clauses_start/num_clauses_start
        else:
            fraction_of_clauses_removed = 0
        
        unassigned_nodes_start = len(list(filter(lambda x: len(x) > 0, literal_clauseNum.values())))
        
        # Do unit prop
        empty_clause, literal_clauseNum, clauseNum_clause, literal_boolen = \
            unit_prop(literal_clauseNum, clauseNum_clause, literal_boolen)
            
        if empty_clause:
            isEmpty = len(self.stack) == 0
            if not isEmpty:
                self.state = self.stack.pop()
            return None, -1 + self.action_penalty[action], isEmpty
        
        if clauseNum_clause == {}:
            return None, 1 + self.action_penalty[action], True
        
        # Do pure literal elimination
        literal_clauseNum, clauseNum_clause, literal_boolen = \
            pure_literal(literal_clauseNum, clauseNum_clause, literal_boolen)
            
        if clauseNum_clause == {}:
            return None, 1 + self.action_penalty[action], True
        
        literal = choose_var(literal_clauseNum, clauseNum_clause, literal_boolen, algo=self.actions[action])
        
        
        # Set the chosen literal to be True
        literal_clauseNum_T, clauseNum_clause_T, literal_boolen_T = \
            set_var(literal, True, deepcopy(literal_clauseNum), deepcopy(clauseNum_clause), dict(literal_boolen))
            
#         print("After setting", literal, "to True")
#         print(literal_clauseNum_T)
#         print(literal_boolen_T)
#         print()
        
#         unassigned_nodes_T = len(filter(lambda x: len(x) > 0, literal_clauseNum_T.values()))
        
#         # Do unit prop and pure literal elimnation and record the number of nodes assigned
#         empty_clause, literal_clauseNum, clauseNum_clause, literal_boolen = 
#             unit_prop(literal_clauseNum_T, clauseNum_clause_T, literal_boolen_T)
        
#         if empty_clause:
#             return 0, 0, unassigned_nodes_start, self.q.empty()
        
#         # Do pure literal elimination
#         literal_clauseNum, clauseNum_clause, literal_boolen = 
#             pure_literal(literal_clauseNum, clauseNum_clause, literal_boolen)
            
#         if clauseNum_clause == {}:
#             return 0, 0, unassigned_nodes_start, True
        
        # Set new state
        self.state = (literal_clauseNum_T, clauseNum_clause_T, literal_boolen_T)
        
        # Set the chosen literal to be False
        literal_clauseNum_F, clauseNum_clause_F, literal_boolen_F = \
            set_var(literal, False, literal_clauseNum, clauseNum_clause, literal_boolen)
            
#         print("After setting", literal, "to False")
#         print(literal_clauseNum_F)
#         print(literal_boolen_F)
#         print()
            
#         unassigned_nodes_F = len(filter(lambda x: len(x) > 0, literal_clauseNum_F.values()))
            
#         # Do unit prop and pure literal elimnation and record the number of nodes assigned
#         empty_clause, literal_clauseNum, clauseNum_clause, literal_boolen = 
#             unit_prop(literal_clauseNum_F, clauseNum_clause_F, literal_boolen_F)
        
#         if empty_clause:
#             return 0, 0, unassigned_nodes_start, self.q.empty()
        
#         # Do pure literal elimination
#         literal_clauseNum, clauseNum_clause, literal_boolen = 
#             pure_literal(literal_clauseNum, clauseNum_clause, literal_boolen)
            
#         if clauseNum_clause == {}:
#             return 0, 0, unassigned_nodes_start, True

        # Add new state to queue
        self.stack.append((literal_clauseNum_F, clauseNum_clause_F, literal_boolen_F))
        
        num_clauses_end = 0
        for clause in clauseNum_clause.values():
            if len(clause) > 0:
                num_clauses_end += 1
        
        if num_clauses_start > 0:
            fraction_of_clauses_removed = (num_clauses_start - num_clauses_end)/num_clauses_start
        else:
            fraction_of_clauses_removed = 0
        
        if clauseNum_clause_T == {} or clauseNum_clause_F == {}:  # We have satisfied
            return None, 1 + self.action_penalty[action], True
        else:
            return None, -1 + self.action_penalty[action] + fraction_of_clauses_removed, False