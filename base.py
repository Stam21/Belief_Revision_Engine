
from sympy.logic.boolalg import And
from sympy import to_cnf, false, Symbol
from sympy.logic.inference import satisfiable
from copy import deepcopy
import numpy as np


def validate_order(p):
    if not (0 <= p <= 10):
       raise false

class Base:

    def __init__(self):
        # The belief base is a dictionary that has as keys the name of its sets and as values tuples that store the order and a list of beliefs with that order.
        self.beliefs = [[10, to_cnf("A & B")],[10, to_cnf("A | B")],[10, to_cnf("B")]]
        self.symbols = set()

    #----------------------------------------------------------------
    # AGM postulates for testing purposes
    #----------------------------------------------------------------
    #beliefs in the form [["A"],["B"]]. CHECK WITH BENCE !!
    def success_contraction(self, beliefs, beliefs_contracted, sentence):
        beliefs = changeBBModel(beliefs)
        iselement_belief=False
        iselement_belief_contracted=False

        for elem2 in beliefs_contracted:
           if(elem2==sentence):
                iselement_belief_contracted=True

        if(iselement_belief==iselement_belief_contracted):
            return True
        else:
                return False

    #beliefs in the form [["A"],["B"]]. CHECK WITH BENCE !!
    def inclusion_contraction(self, beliefs, beliefs_contracted):
        beliefs = changeBBModel(beliefs)
        flag = False
        if(all(x in beliefs for x in beliefs_contracted)):
            flag = True
        return flag

    #beliefs in the form [["A"],["B"]]. CHECK WITH BENCE !!
    def vacuity_contraction(self, beliefs, beliefs_contracted, sentence):
        beliefs = changeBBModel(beliefs)
        if not(entailment(beliefs, sentence)):
            if(beliefs==beliefs_contracted):
                return True
            else:
                return False
        else:
            return True

    #beliefs in the form [["A"],["B"]]. CHECK WITH BENCE !!
    def extensionality_contraction(self, beliefs, beliefs_contracted1, beliefs_contracted2, sentence1, sentence2):
        beliefs = changeBBModel(beliefs)
        if(sentence1==sentence2):
            for elem in beliefs:
               if(elem==sentence1):
                    if(beliefs_contracted1==beliefs_contracted2):
                        return True
                    else:
                        return False
        return True

    def _success(self):#DONE FOR CONTRACTION, EXPANSION ?? GEORGIOS
        return True


    def _inclusion(self, p): #KARRAR
        # K(set of belief) * p(new blief) subset K
        # define set K and p
        K = set(belief[1] for belief in self.beliefs)
        # check if p is already in K
        if  p in K:
            return True

        # Check if K' is a subset of K * p
        K = deepcopy(self.beliefs) # used deepcopy to creat new list of belief K
        def _success(self):
            return True

        def _inclusion(self, p):
            # K(set of belief) * p(new blief) subset K
            # define set K and p
            K = set(belief[1] for belief in self.beliefs)
        # check if p is already in K
            if p in K:
             return True

    # Check if K' is a subset of K * p
        K_p = deepcopy(self.beliefs) # used deepcopy to creat new list of belief K
        #by copying current belief base (self.belief)add p to it

        K_p.append([0, p]) #add p to K'
        for belief in K_p:
            ## 'And' used to combine multi-belief into single expression for input satisfiable
            if satisfiable(And(K, set([belief]))) and not satisfiable(And(K_p)):
                return False  # K * p is not a superset of K + p
        return True # K * p is a superset of K + p

    def _vacuity(self):

        return True


    def _consistency(self,p): # B(K) ∗ φ(p) is consistent if φ(p) is consistent.

        K_p = deepcopy(self.beliefs)
        K_p.append([0, p])
        # Check if B_phi is consistent by checking if it is satisfiable
        return satisfiable(And(set([belief[1] for belief in K_p])))


    def _extensionality(self):
         # if (p<=> p) is set Cn{}, then K ÷ p = K ÷q
        # it gurantee the logical of contraction is extentional
        #create two prositional symbols p and q
        p = Symbol('p')
        q = Symbol('q')
        # create two equivalant propositional formulas
        f1 = p >> q
        f2 = q >> p
        #convert them into to_CNF
        f1_cnf = to_cnf(f1) # we create a belief base using thoses to check
        f2_cnf = to_cnf(f2) #K*f1 is equivalent to K*f2

        # create a belief base with f1, and check that K*f1 equivalent to K*f2
        b = Base()
        #expansion method to expand the belief base bb with given prepositional formula f1-cnf
        #(0.5) is degree of belief represent as number between 0,and 1
        b.expansion(f1_cnf, 0.5) # 0.5 represent moderate degree of belief or uncertainty
        Kf1 = b.get_consequence(to_cnf(p >> f1_cnf)) # logical sequence of B set Cn(B)
        Kf2 = b.get_consequence(to_cnf(p >> f2_cnf))
        assert Kf1 == Kf2, "K*f1 is not eqiuvalent to K*f2"
        # Check that K*f2 is equivalent to K*f1
        Kf2 = b.get_consequence(to_cnf(p >> f2_cnf))
        Kf1 = b.get_consequence(to_cnf( p >>f1_cnf))
        #to verify formulas are equivelant as expect equivalence f1, f2
        assert Kf2 == Kf1, "K*f2 is not equivalent to K*f1"

    #----------------------------------------------------------------

    def tell(self,sen,action, order):


        if not (satisfiable(sen) == false):# why not use: "if satisfiable(sen) != Fasle:" Note: sympy.fasle == False returns True
            if action=='c':
                self.contraction(sen, order)
            elif action=='e':
                self.expansion(sen, order)
        else:
            print("Unsatisfiable Belief")

    '''
     If the agent receives new information that conflicts with one of the beliefs in the knowledge base,
     it will revise its belief base by removing the lower-priority belief and adding the new information in its place.
    '''
    def revision(self, sen, action,  order=0):
        if action == "c":
            return self.revision_contraction(sen)
        elif action == "e":
            return self.revision_expansion(sen, order)

    def revision_expansion(self, sen, order):
        if (entailment(self.beliefs, sen)):
            print("The new beliefe will not be added in order to prevent redundancy.")
            return False
        else:
            statement = "(" + str(sen) + ")"
            for elem in self.beliefs:
                statement = statement + "&(" + str(elem[1]) + ")"

            print(statement)
            if not satisfiable(to_cnf(statement)):
                print("The new belief will not be added as it contradicts a previous belief.")
                #keep the highest order beliefe, if same keep oldest
                return False

            else:
                print("The beliefe", sen, "can be added to the bb with an order of", order)
                return True


    def revision_contraction(self, sen):

        delete = []
        keep = []
        for elem in self.beliefs:
            if elem[1] != to_cnf(sen):
                keep.append(elem)
                if entailment(keep, sen):
                    keep.pop(-1)
                    delete.append(elem)
            else:
                delete.append(elem)

        if len(keep)>0:
            self.beliefs = keep
            print("The following beliefs have been deleted as they entailed the beliefe that was to be removed:")
            for elem in delete:
                print(elem[1])
            return True
        else:
            print("The operation will erase all beliefs due to their entailment, are you sure you want to procede ? Y/N")
            answ = input()
            if (answ == "y"):
                self.beliefs = keep
                print("All beliefs have been deleted")
                return True
            else:
                return False


    # Function for expansion that adds a belief and its consequences in the knowledge base but taking into consideration consistency and contradiction.
    def expansion(self,sen, order):
        if self.revision(sen, "e", order):
            self.beliefs.append([order,sen])


    # Function for contraction that removes a belief and its consequences from the knowledge base.
    def contraction(self,sen):
        self.revision(sen, "c")



    def getKB(self):
        return self.beliefs


# -------------------------------------------------------------------
# Entailment checker for a new belief
# -------------------------------------------------------------------

#beliefs = [[10, to_cnf("A & B")]] 
#entailment(belief, to_cnf("A")) True - Pass
#entailment(belief, to_cnf("B")) False - Fail BP
#entailment(belief, to_cnf("A&B")) True - Pass
#entailment(belief, to_cnf("A|B")) True - Pass
#entailment(belief, to_cnf("A>>B")) False - Fail BP
#entailment(belief, to_cnf("B>>A")) True - Pass
#entailment(belief, to_cnf("(B>>A)&(A>>B)")) True - Pass
#entailment(belief, to_cnf("~(A&B)")) False - Pass
#entailment(belief, to_cnf("~A")) False - Pass
#entailment(belief, to_cnf("~B")) False - Pass

#beliefs = [[10, to_cnf("A")]] 
#entailment(belief, to_cnf("A")) True - Pass
#entailment(belief, to_cnf("B")) False - Pass
#entailment(belief, to_cnf("A&B")) True - Fail P
#entailment(belief, to_cnf("A|B")) True - Pass
#entailment(belief, to_cnf("A>>B")) False - Pass
#entailment(belief, to_cnf("B>>A")) True - Pass
#entailment(belief, to_cnf("(B>>A)&(A>>B)")) True - Fail P
#entailment(belief, to_cnf("~(A&B)")) False - Pass
#entailment(belief, to_cnf("~A")) False - Pass
#entailment(belief, to_cnf("~B")) False - Pass

def entailment(base,sentence):
    
    base = changeBBModel(base)
    #Split the base by the AND operator
    clauses = [clause for f in base for clause in splitByOperator("&",f)]
    clauses += splitByOperator("&",to_cnf(~sentence))
    print("cl", clauses)
    new=[]
    # Check if there is already a False in the clauses
    print("ln", len(clauses))
    for x in range(len(clauses)):
        for y in range(x+1, len(clauses)):
            print("loop")
            #Do nothing when empty clauses are found
            if (clauses[x] == "" or clauses[y] == ""):
                continue

            f = resolve(clauses[x],clauses[y])
            print("f", f)

            #if resolvents contains the empty clause then return true
            for elem in f:
                if elem =="":
                    return True

            #new ←new ∪ resolvents
            new.append(f)
            #new.append(s)

    #if new ⊆ clauses then return false
    for elem in new:
        for elem2 in clauses:
            if not np.array_equal(elem, elem2):
                return False


#belief = ["A"]
#entailment(belief, to_cnf("(B>>A)&(A>>B)"))

def resolve(ci, cj):

    """
    Generate all clauses that can be obtained by applying
    the resolution rule on ci and cj.
    """

    rci = splitByOperator("|",ci)
    rcj = splitByOperator("|",cj)

    copyRci = deepcopy(rci)
    copyRcj = deepcopy(rcj)

    cnti=0
    cntj=0
    for ri in rci:
        cntj=0
        for rj in rcj:

            if to_cnf(ri) == ~to_cnf(rj):
                copyRci[cnti]=""
                copyRcj[cntj]=""
            cntj+=1
        cnti+=1

    #Only care about the updated sentences in the belief set not the sentence
    copyRci=np.unique(copyRci)
    copyRcj=np.unique(copyRcj)

    return np.unique(np.append(copyRci, copyRcj))


#----------------------------------------------------------------
# Utils for the belief revision engine
#----------------------------------------------------------------

def getSymbols(items, clause):
    # Returns a set of symbols used in a clause, removing all operators.
    for it in items:
        clause =  {x for x in clause if x != it}

    return clause

def splitByOperator(op, clause) -> list:

    # e.g If the op is OR and the clause is A | B then it returns [A, B].
    # If the op is AND and the clause is (A|B) & (C|D) then it returns [A|B, C|D].
    strClause = str(clause).replace(" ", "")
    strClause = str(strClause).replace("(", "")
    strClause = str(strClause).replace(")", "")
    splits = strClause.split(op)
    return list(splits)

def changeBBModel(base):
    bb = []
    for elem in base:
        bb.append(elem[1])
    return bb

#----------------------------------------------------------------


#Commented code that might be useful using the getSymbols function and sympy's truth table

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

#----------------------------------------------------------------
