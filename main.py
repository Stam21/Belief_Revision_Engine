
'''
Main function that opens the cli prompt communicates with the belief revision engine.
'''
from sympy import SympifyError, to_cnf
from base import Base


def helper(): 
    print(
    """
    t: Show example of a belief base 
    e: Expansion of belief base
    c: Contraction of belief base
    b: Show belief base
    h: Help
    q: Exit
    """)

def getExamples(): 
    print("""
        BiImplication -> (A>>B) & (B>>A)
        Implication -> (A&B) >> C
        Conjuction -> A & B & C
        Disjunction -> A | B | C
        Negation -> ~A & ~B 

        Belief Base -> {
            "Game1" : [(0.5,[A & B & C , (A>>B) & (B>>A)]), (0.7,[A | B | C])]
            "Game2" : [...]
        }

        In case of invalid sequence even though the operators used and the sequence in general is correct, try to change the letters.
        Letters that are tested are A , B , C , M , N , X , Y , Z
        This is written because of an error arised when letter E was used.
    """)

def parseInput(b):
    helper()
    action = input()
    if action == 't':
        print(f"{getExamples()}")
    elif action == 'e'or action == 'c':
        print("Write the belief for which to apply the selected action")
        sentence = input()
        print("Write the Belief Set that this belief is included")
        bSet = input()
        print("Write the priority order for that belief")
        order = input()
        try:
            sentenceCNF = to_cnf(sentence)
            b.tell(sentenceCNF, action, bSet, order)

        except SympifyError:
            print("Invalid sequence, try again with valid boolean expressions")
    elif action == 'b': 
        for belief in b.getKB():
            print(f"{belief}")
    
    elif action == 'h':
        helper()
    elif action == 'q':
        exit()

    else:
        print('Action not recognized. Type \'h\' for help.')

    parseInput(b)

def main():
   
    b = Base()
    parseInput(b)
    

if __name__ == '__main__':
    main()