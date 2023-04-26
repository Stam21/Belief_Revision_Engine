from copy import deepcopy

from sympy.logic.boolalg import to_cnf, Or, And, truth_table, Equivalent
from sympy import Symbol, symbols, to_cnf, false
from sympy.logic.inference import satisfiable
from decimal import Decimal




def validate_order(p):
    if not (0 <= p <= 10):
       raise false
    
class Base:

    def __init__(self):
        # The belief base is a dictionary that has as keys the name of its sets
        #  and as values tuples that store the order and a list of beliefs with that order.
        self.beliefs = [[10, to_cnf("A & B")],[1, to_cnf("B & C")]]
        self.symbols = set()
        self._reorder_beliefs_line = []

        # each belief assigned an order(between 0 and 1)
    #def _add_reorder_belief_line(self, formula, order):
     #   self._reorder_beliefs_line.append(formula, Decimal(order))

    # run commands in change the order of queue
    def _run_reorder_belief_line(self):
        for sen, order in self._reorder_beliefs_line:
            self.symbols.remove(sen)  # then ignore sen(belief) with order 0
            if order > 0:
                sen.order = order
                self.symbols.add(sen)
        self._add_reorder_belief_line = []        

    # ----------------------------------------------------------------
    # AGM postulates for testing purposes
    # ----------------------------------------------------------------

    def _closure(self):
        return True

    def _success(self):
        return True
#_____________________________________-
    def _inclusion(self):  # K(set of belief) * p(new blief) subset K + p
    # define set K and p
        K = set(belief[1] for belief in self.beliefs)
    # check if p is already in K
        if p in K:    
         return True
        
    # Check if K' is a subset of K * p 
        K = deepcopy(self.beliefs) # used deepcopy to creat new list of belief K
        #by copying current belief base (self.belief)add p to it

        K.append([0, p]) #add p to K'
        for belief in K:
            ## 'And' used to combine multi-belief into single expression for input satisfiable
            if satisfiable(And(*K - set([belief]))) and not satisfiable(And(*K)):
                return False  # K * p is not a superset of K + p
            
        return True # K * p is  a superset of K + p   

    def _vacuity(self):   # if not p (is not set)K, then K*p = K+p
        return True

    def _consistency(self):  # ask the professor about it
        return True
#____________________________________________
    def _extensionality(self):   # if (p<=> p) is set Cn{}, then K*p = K *p
        ## p = Equivalent('p', 'p')
        #return True 
        #satisfiable(to_cnf(Or(p, ~q))) == False

        #create two prositional symbols p and q
        p = Symbol('p')
        q = Symbol('q')
        # create two equivalant propositional formulas
        f1 = Equivalent(p, q) # f1= fia, f2 = sia
        f2 = Equivalent (q, p)
        #convert them into to_CNF
        f1_cnf = to_cnf(f1) # we create a belief base using thoses to check
        f2_cnf = to_cnf(f2) #K*f1 is equivalent to K*f2

        # create a belief base with f1, and check that K*f1 equivalent to K*f2
        bb = Base()
        #expansion method to expand the belief base bb with given prepositional formula f1-cnf
        #(0.5) is degree of belief represent as number between 0,and 1
        bb.expansion(f1_cnf, 0.5) # 0.5 represent moderate degree of belief or uncertainty 
        Kf1 = bb.get_consequence(to_cnf(And(K, f1_cnf))) # logical sequence of B set Cn(B)
        Kf2 = bb.get_consequence(to_cnf(And(K, f2_cnf))) 
        assert Kf1 == Kf2, "K*f1 is not eqiuvalent to K*f2"
        # Check that K*f2 is equivalent to K*f1
        Kf2 = bb.get_consequence(to_cnf(And(K, f2_cnf)))
        Kf1 = bb.get_consequence(to_cnf(And(K, f1_cnf)))
        #to verify formulas are equivelant as expect equivalence f1, f2
        assert Kf2 == Kf1, "K*f2 is not equivalent to K*f1"

        #return(p == q)

    # ----------------------------------------------------------------

    def tell(self, sen, action, order):

        # why not use: "if satisfiable(sen) != Fasle:" Note: sympy.fasle == False returns True
        if not (satisfiable(sen) == false):
            if action == 'c':
                self.contraction(sen, order)
            elif action == 'e':
                self.expansion(sen, order)
        else:
            print("Unsatisfiable Belief")

    '''
     If the agent receives new information that conflicts with one of the beliefs in the knowledge base, 
     it will revise its belief base by removing the lower-priority belief and adding the new information in its place.
    '''
    def degree(self, sentence): 
        sentence =  to_cnf(sentence)
        if entailment([], sentence): # totualogy has degree = 1

            return Decimal(1)

    # Function for expansion that adds a belief and its consequences in the knowledge base but taking into consideration consistency and contradiction.
    def expansion(self, sen, order):
        '''
         Update entrench ranks for belief base expansion

         Parameters: () to check if trure, the formula will + to BelifeB after rank is update
        '''
        p = to_cnf(sen)
        order = order
      
        
        if not entailment(self.beliefs,  ~p):
            # if p is a contradict, ignore
            if entailment([], p):
                # if p is a tautology, assign the order to 1
                order = (1)
            else:
                self.beliefs.append([order, p])

                return 0
                    
                    
    # Function for contraction that removes a belief and its consequences from the knowledge base.

    def contraction(self, sen, order):
        for elem in self.beliefs:
            if (elem[1] == sen):
                self.beliefs.remove(elem)
                break

    def getKB(self):
        return self.beliefs


# -------------------------------------------------------------------
# Entailment checker for a new belief
# -------------------------------------------------------------------
def entailment(base, sentence):

    clauses = [clause for f in base for clause in splitByOperator("&", f[1])]

    # Add negation of formula to clauses
    clauses += splitByOperator("&",to_cnf(~sentence))

    # Check if there is already a False in the clauses
    if False in clauses:
        return True

    print("fC", clauses)
    for x in range(len(clauses)):
        for y in range(x+1, len(clauses)):
            if (clauses[x] == "" or clauses[y] == ""):
                continue
            f,s = resolve(clauses[x],clauses[y])
            print("resolvants",f,s)
            firstS = ""
            if len(f)>0:
                firstS = list(f)[0]
                for elem in list(f)[1:]:
                    firstS = firstS+"|"+elem
            clauses[x] = firstS
            
            secondS = ""
            if len(s)>0:
                secondS = list(s)[0]
                for elem in list(s)[1:]:
                    secondS = secondS+"|"+elem
            clauses[y] = secondS
            print("clases",clauses)
            
                
    return len(clauses) == clauses.count("")


def resolve(ci, cj):
    # does tis code sccount for the posibility of different
    # elements of ci or cj canceling amongst themselfs ?
    """
    Generate all clauses that can be obtained by applying
    the resolution rule on ci and cj.
    """

    rci = splitByOperator("|",ci)
    rcj = splitByOperator("|",cj)
    print("rci", rci, "rcj", rcj)
    copyRci = deepcopy(rci)
    copyRcj = deepcopy(rcj)
    for ri in rci:
        for rj in rcj:
            #print(ri,rj)
            if to_cnf(ri) == ~to_cnf(rj):
                copyRci.discard(ri)
                copyRcj.discard(rj)
    return copyRci, copyRcj


# ----------------------------------------------------------------
# Utils for the belief revision engine
# ----------------------------------------------------------------

def getSymbols(items, clause):
    # Returns a set of symbols used in a clause, removing all operators.
    for it in items:
        clause = {x for x in clause if x != it}

    return clause


def splitByOperator(op, clause: str) -> list:
    # e.g If the op is OR and the clause is A | B then it returns [A, B].
    # If the op is AND and the clause is (A|B) & (C|D) then it returns [A|B, C|D].
    strClause = str(clause).replace(" ", "")
    strClause = str(strClause).replace("(", "")
    strClause = str(strClause).replace(")", "")
    splits = strClause.split(op)
    return set(splits)


# ----------------------------------------------------------------


# Commented code that might be useful using the getSymbols function and sympy's truth table

# NewSymbols = set(getSymbols(['|','&','>>','~','(',')',' '],str(sentence)))
# negated_sentence = to_cnf(~sentence)
# # For every sentence in the knowledge base, we have to check for validity and satisfiability of the new sentence.
# for sen in base:
#     # Check only the sentences in which we can find symbols that are also in the new sentence.
#     Symbols = set(getSymbols(['|','&','>>','~','(',')',' '],str(sen)))
#     common_symbols = NewSymbols.intersection(Symbols)
#     truth_table_New =  truth_table(sentence, common_symbols)
#     truth_table_Current = truth_table(sen, common_symbols)
#     validity = True
#     # if (Equivalent(sentence,sen)):

#     # if equivelant is true then break and it is entailed
#     for a, b in zip(truth_table_Current, truth_table_New):
#         if (a[1]== True) and (b[1]==False):
#             validity = False

# ----------------------------------------------------------------
#The operator 'K' used to donate 'an agent'.n the context of the code, 
# it is being used in the AGM postulates for testing purposes to represent 
# the operator used to modify a set of beliefs. Specifically, the postulate 
# being tested is: "If (p<=> p) is set Cn{}, then K*p = K *p"
#Here, 'Kp' represents the set of all beliefs that an agent knows that 'p',
# and 'Kp' represents the set of all beliefs that an agent  
#knows that 'p' if the belief 'p<=>p' (that is, the belief that 'p' 
# is logically equivalent to itself) 

#__ __ __ __ __ #
# get-consequence is to verify the expensionality axiom of logical system which states:
#two formula logically equivalent, then the agent's knowledge of one
#implies knowledge of the other.
# The agent knowledge of. Kf1 must be equivl to their knowledge as kf2 due to f1 & f2
#are logically equivlent
# __ __ __ __ __ #