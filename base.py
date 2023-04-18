
from sympy.logic.boolalg import Or, And, truth_table, Equivalent
from sympy import to_cnf
from sympy.logic.inference import satisfiable

class Base:

    def __init__(self):
        # The belief base is a dictionary that has as keys the name of its sets and as values tuples that store the order and a list of beliefs with that order.
        self.beliefs = { }
        self.symbols = set()
  
    #----------------------------------------------------------------
    # AGM postulates for testing purposes
    #----------------------------------------------------------------
    def _success():
        return True
    def _inclusion():
        return True
    def _vacuity():
        return True
    def _consistency():
        return True
    def _extensionality():
        return True
    #----------------------------------------------------------------
    
    def tell(self,sen,action, bSet, order):

        models = satisfiable(sen, all_models=True)
        sat = False
        for model in models:
            if model:
                # Do something with the model.
                sat = True
            else:
                # Given expr is unsatisfiable.
                print("Unsatisfiable Belief")

        if sat:
            if action=='r': 
                self.revision(sen)
            elif action=='c':
                self.contraction(sen)
            elif action=='e':
                self.expansion(sen)
        

    '''
     If the agent receives new information that conflicts with one of the beliefs in the knowledge base, 
     it will revise its belief base by removing the lower-priority belief and adding the new information in its place.
    '''
    def revision(self, sen):
        self.beliefs.append(sen)
        print(sen)

    # Function for expansion that adds a belief and its consequences in the knowledge base but taking into consideration consistency and contradiction.    
    def expansion(self,sen):
        self.beliefs.append(sen)

    # Function for contraction that removes a belief and its consequences from the knowledge base.
    def contraction(self,sen):
        self.beliefs.remove(sen)

    


# -------------------------------------------------------------------
# Entailment checker for a new belief
# -------------------------------------------------------------------
def entailment(base,sentence):
    
    clauses = [clause for f in base for clause in splitByOperator(And,f)]
    
    # Add negation of formula to clauses
    clauses += splitByOperator(Or,~sentence)

    # Check if there is already a False in the clauses
    if False in clauses:
        return True

    while True:
        new_clauses = set()

        # Generate all possible pairs of clauses for resolution
        for i, ci in enumerate(clauses):
            for j, cj in enumerate(clauses):
                if i >= j:
                    continue

                # Try to resolve ci and cj
                resolvents = resolve(ci, cj)

                # Check if resolvents contain False
                if any(resolvent == False for resolvent in resolvents):
                    return True

                # Add non-tautological resolvents to new_clauses
                new_clauses |= {resolvent for resolvent in resolvents if resolvent != True and resolvent not in clauses}

        # Check if all new_clauses are already in clauses
        if all(clause in clauses for clause in new_clauses):
            return False

        # Update clauses with new_clauses
        clauses += list(new_clauses)

def resolve(ci, cj):
    """
    Generate all clauses that can be obtained by applying
    the resolution rule on ci and cj.
    """

    rci = splitByOperator(Or,ci)
    rcj = splitByOperator(Or,cj)
    resolvents = {(rci - {ri}) | (rcj - {rj}) for ri in rci for rj in rcj if ri == ~rj or ~ri == rj}
    sorted_resolvents = []
    for resolvent in resolvents:
        resolvent = list(resolvent)
        resolvent.sort(key=str)
        sorted_resolvents.append(Or(*resolvent))
    return sorted_resolvents


#----------------------------------------------------------------
# Utils for the belief revision engine
#----------------------------------------------------------------

def getSymbols(items, clause):
    # Returns a set of symbols used in a clause, removing all operators. 
    for it in items:
        clause =  {x for x in clause if x != it}
    
    return clause

def splitByOperator(op, clause : str) -> list:

    # e.g If the op is OR and the clause is A | B then it returns [A, B].
    # If the op is AND and the clause is (A|B) & (C|D) then it returns [A|B, C|D].
    splits = []
    stack = list(clause)

    while stack:
        arg = stack.pop()
        if arg.op == op:
            stack.extend(reversed(arg.clause))
        else:
            splits.append(arg)

    return splits



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