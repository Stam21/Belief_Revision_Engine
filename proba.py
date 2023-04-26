from sympy.logic.boolalg import Not, Or, And, truth_table, Equivalent 
from sympy.logic import simplify_logic
from sympy import to_cnf, false
from sympy.logic.inference import satisfiable
import sympy
from copy import deepcopy
import numpy as np

def success(beliefs, beliefs_contracted, sentence):
        
    for element in beliefs:

        if(sympy.logic.inference.valid(element)):
            if(sympy.logic.inference.inference_algorithm(beliefs_contracted, sentence)==False):
                print("Success")


def contraction(beliefs,sen):
        for elem in beliefs:
            if (elem == sen):
                beliefs.remove(elem)
                break        

def splitByOperator(op, clause : str) -> list:

    # e.g If the op is OR and the clause is A | B then it returns [A, B].
    # If the op is AND and the clause is (A|B) & (C|D) then it returns [A|B, C|D].
    splits = []
    stack = str(clause)

    op_index=0
    for elem in range(0, len(stack)):
        
        if stack[elem] == op:

            splits[elem]=stack[op_index, elem]
            op_index=elem+1
            

    return splits

def splitByOperator(op, clause) -> list:

    # e.g If the op is OR and the clause is A | B then it returns [A, B].
    # If the op is AND and the clause is (A|B) & (C|D) then it returns [A|B, C|D].
    strClause = str(clause).replace(" ", "")
    splits = strClause.split(op)
    return list(splits)

def entailment(base,sentence):

    
    '''
    print(base, sentence)
    #Add the not alphas to the base, by iterating through the base and adding the not alphas to each element
    for f in range(0, len(base)):
        base[f]=to_cnf(And(base[f],sentence))
    
    print(base)
    
    #Convert the base to a list of strings and remove the parenthesis
    list(base)
    for f in range(0, len(base)):
        base[f]=str(base[f])
        if "(" in base[f]:
            base[f]=base[f].replace("(", "")
        if ")" in base[f]:
            base[f]=base[f].replace(")", "")
    '''
    #Split the base by the AND operator   
    clauses = [clause for f in base for clause in splitByOperator("&",f)]
    clauses += splitByOperator("&",to_cnf(~sentence))
    print(clauses, "clauses")
    

    # Check if there is already a False in the clauses
    
    for x in range(len(clauses)):
        for y in range(x+1, len(clauses)):
            #Do nothing when empty clauses are found
            if (clauses[x] == "" or clauses[y] == ""):
                continue
            f,s = resolve(clauses[x],clauses[y])
            
            

            #if resolvents contains the empty clause then return true
            if "" in f or "" in s:
                return True
               
            #new ←new ∪ resolvents
            new.append(f)
            new.append(s)

    #if new ⊆ clauses then return false 
    for elem in new:
        i=0
        for elem2 in clauses:
            if np.array_equal(elem, elem2):
                i=+1
        if(i==0):
            return False
    
    
    #clauses ←clauses ∪new            
    for elem in new:
        if elem not in clauses:
            clauses.append(elem)

 
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
            print(ri, rj)
            
            '''
            not_copyRci=~(copyRci[ri])
            not_copyRcj=~(copyRcj[rj])
            negateRi=str(not_copyRci)
            negateRj=str(not_copyRcj)
            if copyRci[ri] == negateRj or negateRi == copyRcj[rj]:
                copyRci[ri]=""
                copyRcj[rj]=""
            
            if("~" in copyRci[ri]):
                negateRi = copyRci[ri].replace("~", "")
            else:
                negateRi = Not(copyRci[ri]) 
            
            if("~" in copyRcj[rj]):
                negateRj = copyRcj[rj].replace("~", "")
            else:
                negateRj = Not(copyRcj[rj]) 
            negateRi=str(negateRi)
            negateRj=str(negateRj)
            print(rci[ri], negateRj, negateRi, copyRcj[rj])
            '''
            #if to_cnf(ri) == ~to_cnf(rj) or ~to_cnf(ri) == to_cnf(rj):
            if to_cnf(ri) == ~to_cnf(rj):
                copyRci[cnti]=""
                copyRcj[cntj]="" 
            cntj+=1
        cnti+=1
    
   
    copyRci=np.unique(copyRci)
    copyRcj=np.unique(copyRcj)          
    return copyRci, copyRcj
    


#Example beelief set and sentence


beliefs = [to_cnf("A|B")]
sentence = to_cnf("B")
#Check whether the entailment returns true or false
if(entailment(beliefs, sentence)):
    print(True)
else:
    print(False)    



#print(splitByOperator("&", beliefs[0]))
#senten=And(beliefs,  sen)
#print(senten)
#print(to_cnf(senten))

#beliefs = [to_cnf("~A|A"), to_cnf("B|~B")]
#belief_base=beliefs
#contraction(beliefs, to_cnf("B"))

#success(belief_base, beliefs, to_cnf("B|~B"))




