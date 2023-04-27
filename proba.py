from sympy.logic.boolalg import Not, Or, And, truth_table, Equivalent 
from sympy.logic import simplify_logic
from sympy import to_cnf, false
from sympy.logic.inference import satisfiable
import sympy
from copy import deepcopy
import numpy as np

def success(beliefs, beliefs_contracted, sentence):
        iselement_belief=False
        iselement_belief_contracted=False
        for elem in beliefs:
           if(elem==sentence):
                iselement=True
        
        for elem2 in beliefs_contracted:
           if(elem2==sentence):
                iselement_belief_contracted=True  
               
        if(iselement_belief==iselement_belief_contracted):
            return True
        else:
            return False    
    


def contraction(beliefs,sen):
        
        if(entailment(beliefs, sen)):
            return True
        else:
            return False
          
                       



def splitByOperator(op, clause) -> list:

    # e.g If the op is OR and the clause is A | B then it returns [A, B].
    # If the op is AND and the clause is (A|B) & (C|D) then it returns [A|B, C|D].
    strClause = str(clause).replace(" ", "")
    splits = strClause.split(op)
    return list(splits)

def entailment(base,sentence):

    #Split the base by the AND operator   
    clauses = [clause for f in base for clause in splitByOperator("&",f)]
    clauses += splitByOperator("&",to_cnf(~sentence))
    
    new=[]
    # Check if there is already a False in the clauses
    
    for x in range(len(clauses)):
        for y in range(x+1, len(clauses)):
            #Do nothing when empty clauses are found
            if (clauses[x] == "" or clauses[y] == ""):
                continue
            
            f = resolve(clauses[x],clauses[y])
            
            #if resolvents contains the empty clause then return true
            inc=0
            for elem in f:
                if elem !="":
                    inc=inc+1
            if(inc==0):
                return True
              
            #new ←new ∪ resolvents
            new.append(f)
            #new.append(s)

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
            
            if to_cnf(ri) == ~to_cnf(rj):
                copyRci[cnti]=""
                copyRcj[cntj]="" 
            cntj+=1
        cnti+=1
    
    #Only care about the updated sentences in the belief set not the sentence
    copyRci=np.unique(copyRci)
    
    return copyRci
    


#Example beelief set and sentence


beliefs = ["A&B&C&D", "A&B"]
sentence = to_cnf("B")

#Testing code for entailment
'''
if(entailment(beliefs, sentence)):
    print(True)
else:
    print(False)    

'''
#Section for calling contraction
#create a copy in order to eliminate the issues arising with indexing

copy_beliefs=deepcopy(beliefs)
cnt=0

for elem in beliefs:
    curr_beliefs=[to_cnf(elem)]
    print("curr elem: ", elem)
    
    if(contraction(curr_beliefs, sentence)):
       
        del copy_beliefs[cnt]
        cnt=cnt-1
    cnt=cnt+1
print(copy_beliefs)



#Testing section for the Success postulate, should return true

print(success(beliefs, copy_beliefs, sentence))


#success(beliefs, , sentence)