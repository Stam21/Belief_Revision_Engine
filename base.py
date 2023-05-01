
from sympy.logic.boolalg import And
from sympy import to_cnf, false, Symbol
from sympy.logic.inference import satisfiable
from copy import deepcopy
import numpy as np


def validate_order(p):
    if not (0 <= p <= 10):
       raise false


class Base:

    def __init__(self, beliefs=[[10, to_cnf("A & B")],[10, to_cnf("A | B")],[10, to_cnf("B")]]):
        # The belief base is a dictionary that has as keys the name of its sets and as values tuples that store the order and a list of beliefs with that order.
        self.beliefs = beliefs
        self.symbols = set()

    #----------------------------------------------------------------
    # AGM postulates for testing purposes
    #----------------------------------------------------------------

    def success_contraction(self, beliefs, beliefs_contracted, sentence): #DONE
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
            
    def inclusion_contraction(self, beliefs, beliefs_contracted): #DONE
        flag = False
        if(all(x in beliefs for x in beliefs_contracted)):
            flag = True
        return flag

    def vacuity_contraction(self, beliefs, beliefs_contracted, sentence): #DONE
        if not(entailment(beliefs, sentence)):
            if(beliefs==beliefs_contracted):
                return True
            else:
                return False
        else:
            return True

    def extensionality_contraction(self, beliefs, beliefs_contracted1, beliefs_contracted2, sentence1, sentence2): #DONE
        beliefs = changeBBModel(beliefs)
        if(sentence1==sentence2):
            for elem in beliefs:
               if(elem==sentence1):
                    if(beliefs_contracted1==beliefs_contracted2):
                        return True
                    else:
                        return False
        return True

    def success_expansion(self, sen):
        return entailment(self.beliefs, to_cnf(sen))
        
    def vacuity_expansion(self, beliefs_init, sen, order):
        beliefs_init.append([order, sen])
        if not(entailment(beliefs_init, to_cnf(~sen))):

            if(self.beliefs==beliefs_init):
                return True
            else:
                return False
        else:
            return True
    
    def inclusion_expansion(self, bb, sen, revisedBb): #NEEDS TO BE TESTED
        if (self.consistency_expansion(bb,sen)):
            revisedBbForm = "(" + str(sen) + ")"
            for elem in revisedBb:
                revisedBbForm = revisedBbForm + "&(" + str(elem[1]) + ")"
            bb = deepcopy(bb)
            bb.append([0,sen])
            if (entailment(bb, to_cnf(revisedBbForm))):
                return True
            else:
                return False  
        else:
            return False

    def consistency_expansion(self,bb, sen):
        statement = "(" + str(sen) + ")"
        for elem in self.beliefs:
            statement = statement + "&(" + str(elem[1]) + ")"

        return satisfiable(to_cnf(statement))


    def extensionality_expansion(self, beliefs, beliefs_expanded1, beliefs_expanded2, sentence1, sentence2): #DONE
        beliefs = changeBBModel(beliefs)
        if(sentence1==sentence2):
            for elem in beliefs:
               if(elem==sentence1):
                    if(beliefs_expanded1==beliefs_expanded2):
                        return True
                    else:
                        return False
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
    def testExpansionAGMPostulates(self, bb, revisedBb, sen, order):
        if (self.consistency_expansion(bb, sen)):
            print("The operation was consistent.")
        else:
            print("FAIL. The operation was not consistent.")
            
        if (self.inclusion_expansion(bb, sen, revisedBb)):
            print("The operation was inclusive.")
        else:
            print("FAIL. The operation was not inclusive.")
            
        if (self.success_expansion(sen)):
            print("The operation was succesfull.")
        else:
            print("FAIL. The operation was not succesfull.")
            
        if (self.vacuity_expansion(bb, sen, order)):
            print("The operation was vacuous.")
        else:
            print("FAIL. The operation was not vacuous.")
        
        b=deepcopy(self)
        c=deepcopy(b)
        test_extensionality_expansion(b, c, sen)
            
        
    def testContractionAGMPostulates(self, bb, revisedBb, sen, order):
            
        if (self.inclusion_contraction(bb, revisedBb)):
            print("The operation was inclusive.")
        else:
            print("FAIL. The operation was not inclusive.")
            
        if (self.success_contraction(bb, revisedBb, sen)):
            print("The operation was succesfull.")
        else:
            print("FAIL. The operation was not succesfull.")
            
        if (self.vacuity_contraction(bb, revisedBb, sen)):
            print("The operation was vacuous.")
        else:
            print("FAIL. The operation was not vacuous.")
        
        b=deepcopy(self)
        c=deepcopy(b)
        test_extensionality_contraction(b, c, sen)
    
    def revision(self, sen, action,  order=0):
        ret = False
        bb = deepcopy(self.beliefs)
        if action == "c":
            ret = self.revision_contraction(sen, order)
        elif action == "e":
            ret = self.revision_expansion(sen, order)
           
        #print("ret", ret)  
        if ret:
            revisedBb = deepcopy(self.beliefs)
            if action == "c":
                self.testContractionAGMPostulates(bb, revisedBb, sen, order)
            elif action == "e":
                self.testExpansionAGMPostulates(bb, revisedBb, sen, order)
        return ret

    def revision_expansion(self, sen, order, mute=False):
        if (entailment(self.beliefs, sen)):
            if not mute:
                print("The new beliefe will not be added in order to prevent redundancy.")
            return False
        else:
            if not self.consistency_expansion(self.beliefs, sen):
                if not mute:
                    print("The new belief will not be added as it contradicts a previous belief.")
                return False

            else:
                if not mute:
                    print("The beliefe", sen, "can be added to the bb with an order of", order)
                self.beliefs.append([order,sen])
                return True

    def revision_contraction(self, sen, order, mute=False):
        delete = []
        highestDeleteOrder = -1
        keep = []
        for elem in self.beliefs:
            if elem[1] != to_cnf(sen):
                keep.append(elem)
                if entailment(keep, sen):
                    keep.pop(-1)
                    delete.append(elem)
                    if (elem[0]>highestDeleteOrder):
                        highestDeleteOrder = elem[0]
            else:
                if (elem[0]>highestDeleteOrder):
                    highestDeleteOrder = elem[0]
                delete.append(elem)

        if len(keep)>0:
            if highestDeleteOrder <= order:
                self.beliefs = keep
                if len(delete)>0:
                    if not mute:
                        print("The following beliefs have been deleted as they entailed the beliefe that was to be removed:")
                    for elem in delete:
                        print(elem[1])
                    return True
                else:
                    if not mute:
                        print("The element is neither a part of the BB nor is it entailed by it. Therefore no believes will be removed.")
            else:
                if not mute:
                    print("The contraction will not take place as it would remove one or more formulas with a higher priority than the one stated for the operation (", highestDeleteOrder, ">", order,")")
        else:
            answ = "y"
            if not mute:
                print("The operation will erase all beliefs due to their entailment, are you sure you want to procede ? y/n")
                answ = input()
            if (answ == "y"):
                self.beliefs = keep
                if not mute:
                    print("All beliefs have been deleted")
                return True
        return False

        #Check with the postulates whether the contraction was successful
        #if not(self.success_contraction(init_beliefs, keep, sen) or self.inclusion_contraction(init_beliefs, keep) or self.vacuity_contraction(init_beliefs, keep, sen)):
        #    print("Error! The contraction did not respect the postulates.")
        #else:
        #    print("All Good! The contraction did respect the postulates.")


    # Function for expansion that adds a belief and its consequences in the knowledge base but taking into consideration consistency and contradiction.
    def expansion(self,sen, order):
        self.revision(sen, "e", order)
            


    # Function for contraction that removes a belief and its consequences from the knowledge base.
    def contraction(self,sen, order):
        self.revision(sen, "c", order)



    def getKB(self):
        return self.beliefs


# -------------------------------------------------------------------
# Entailment checker for a new belief
# -------------------------------------------------------------------
def entaiment_tests():
    beliefs = [[10, to_cnf("A & B")]] 
    print("1", entailment(beliefs, to_cnf("A")) == True)# True - Pass
    print("2", entailment(beliefs, to_cnf("B")) == True)# True - Pass
    print("3", entailment(beliefs, to_cnf("A&B"))== True)# True - Pass
    print("4", entailment(beliefs, to_cnf("A|B"))== True)# True - Pass
    print("5", entailment(beliefs, to_cnf("A>>B"))== True)# True - Pass
    print("6", entailment(beliefs, to_cnf("B>>A"))== True)# True - Pass
    print("7", entailment(beliefs, to_cnf("(B>>A)&(A>>B)"))== True)# True - Pass
    print("8", entailment(beliefs, to_cnf("~(A&B)"))== False)# False - Pass
    print("9", entailment(beliefs, to_cnf("~A"))== False)# False - Pass
    print("10", entailment(beliefs, to_cnf("~B"))== False)# False - Pass
    print("11", entailment(beliefs, to_cnf("~A&B"))== False)# False - Pass
    print("12",entailment(beliefs, to_cnf("~B&A"))== False)# False - Pass
    

    beliefs = [[10, to_cnf("A")]]
    print("1", entailment(beliefs, to_cnf("A"))== True)# True - Pass
    print("2", entailment(beliefs, to_cnf("B"))== False)# False - Pass
    print("3", entailment(beliefs, to_cnf("A&B"))== False)# False -Pass
    print("4", entailment(beliefs, to_cnf("A|B"))== True)# True - Pass
    print("5", entailment(beliefs, to_cnf("A>>B"))== False)# False - Pass
    print("6", entailment(beliefs, to_cnf("B>>A"))== True)# True - Pass
    print("7", entailment(beliefs, to_cnf("(B>>A)&(A>>B)"))== False)# Fasle- Pass
    print("8", entailment(beliefs, to_cnf("~(A&B)"))== False)# False - Pass
    print("9", entailment(beliefs, to_cnf("~A"))== False)# False - Pass
    print("10", entailment(beliefs, to_cnf("~B"))== False)# False - Pass
    print("11", entailment(beliefs, to_cnf("~A&B"))== False)# False - Pass
    print("12", entailment(beliefs, to_cnf("~B&A"))== False)# True - Fail P
    
    beliefs = [[10, to_cnf("A | B")]]
    print("1", entailment(beliefs, to_cnf("A|B"))== True)# True - Pass
    
    beliefs = [[10, to_cnf("A >> B")]]
    print("1", entailment(beliefs, to_cnf("A>>B"))== True)# True - Pass
    
    beliefs = [[10, to_cnf("(A >> B) & (B>>A)")]]
    print("1", entailment(beliefs, to_cnf("(A >> B) & (B>>A)"))== True)# True - Pass
    
    beliefs = [[10, to_cnf("~A")]]
    print("1", entailment(beliefs, to_cnf("~A"))== True)# True - Pass
    

def getExpresion(sen):
    exp = ""
    for idx in range(0,len(sen)):
        if (sen[idx] != ""):
            exp = exp + sen[idx] +"|"
    return exp[0:-1]


def entailment(base,sentence):
    
    base = changeBBModel(base)
    #Split the base by the AND operator
    clauses = [clause for f in base for clause in splitByOperator("&",f)]
    clauses += splitByOperator("&",to_cnf(~sentence))
    #print("cl", clauses)
    new=[]
    tempClauses = deepcopy(clauses)
    for x in range(len(clauses)):
        tempX = np.unique(splitByOperator("|",clauses[x]))
        for y in range(x+1, len(clauses)):
            #print("loop")
            #Do nothing when empty clauses are found
            if (clauses[x] == "" or clauses[y] == ""):
                continue

            f = resolve(clauses[x],clauses[y])
            clauses[y] = getExpresion(f[1])
            #print("TEMPX", tempX, "F0", f[0])
            for idx in range(len(tempX)):
                #print("elem", tempX[idx])
                if not tempX[idx] in f[0]:
                    tempX[idx] = ""
            f = np.unique(np.append(f[0],f[1]))

            #if resolvents contains the empty clause then return true
            dist = False
            for elem in f:
                if elem !="":
                    dist = True
                    
            if not dist:
                return True
            
            #new ←new ∪ resolvents
            new.append(f)
            #new.append(s)
        #print(tempX)
        clauses[x] =getExpresion(tempX)
        #print("cl", clauses)
    
    dist = False
    for elem in clauses:
        if elem !="":
            dist = True
            
    if not dist:
        return True
        
    clauses = tempClauses
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
    return list(splits)

def changeBBModel(base):
    bb = []
    for elem in base:
        bb.append(elem[1])
    return bb

#----------------------------------------------------------------
#Test case for checking the contraction extensionality postulate


def test_extensionality_contraction(base1: Base, base2: Base, sen):
    
    beliefs1=base1.getKB()

    beliefs_contracted1=base1.revision_contraction(sen, 2, True)
    beliefs_contracted2=base2.revision_contraction(sen, 2, True)


    if(base1.extensionality_contraction(beliefs1, beliefs_contracted1, beliefs_contracted2, sen, sen)):
        print("All Good! The contraction did respect the extensionality postulate.")
    else:
        print("The contraction did not respect the extensionality postulate.")
        
#Test case for checking the contraction extensionality postulate
'''
b=Base()
c=Base()
sen=to_cnf("A&B")
test_extensionality_contraction(b, c, sen)
'''
#Test case for checking the contraction extensionality postulate
def test_extensionality_expansion(base1: Base, base2: Base, sen):

    beliefs1=base1.getKB()

    beliefs_expanded1=base1.revision_expansion(sen, 2, True)
    beliefs_expanded2=base2.revision_expansion(sen, 2, True)


    if(base1.extensionality_expansion(beliefs1, beliefs_expanded1, beliefs_expanded2, sen, sen)):
        print("All Good! The expansion did respect the extensionality postulate.")
    else:
        print("The expansion did not respect the expansion extensionality postulate.")

#Test case for checking the expansion extensionality postulate
'''
b=Base()
c=Base()
sen=to_cnf("A&B")
test_extensionality_expansion(b, c, sen)
'''
