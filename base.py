
from sympy.logic.boolalg import Or, And, truth_table, Equivalent 
from sympy import to_cnf, false
from sympy.logic.inference import satisfiable

from copy import deepcopy

class Base:

    def __init__(self):
        # The belief base is a dictionary that has as keys the name of its sets and as values tuples that store the order and a list of beliefs with that order.
        self.beliefs = [[10, to_cnf("A & B")],[1, to_cnf("B & ~A")]]
        self.symbols = set()
  
    #----------------------------------------------------------------
    # AGM postulates for testing purposes
    #----------------------------------------------------------------
    #def _closure(self):
    #    return True
    def _success(self):
        return True
    def _inclusion(self):
        return True
    def _vacuity(self):
        return True
    def _consistency(self):
        return True
    def _extensionality(self):
        return True
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
    def revision(self, sen, order):
        self.beliefs.append([order,sen])

    # Function for expansion that adds a belief and its consequences in the knowledge base but taking into consideration consistency and contradiction.    
    def expansion(self,sen, order):
        entailment([], sen)
        self.beliefs.append([order,sen])
       

    # Function for contraction that removes a belief and its consequences from the knowledge base.
    def contraction(self,sen, order):
        for elem in self.beliefs:
            if (elem[1] == sen):
                self.beliefs.remove(elem)
                break
            
    def getKB(self):
        return self.beliefs


# -------------------------------------------------------------------
# Entailment checker for a new belief
# -------------------------------------------------------------------
def entailment(base,sentence):
    
    clauses = [clause for f in base for clause in splitByOperator("&",f[1])]
    
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
    return set(splits)



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