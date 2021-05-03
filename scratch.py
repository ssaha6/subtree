import cProfile
import pprofile

profiler = pprofile.Profile()
# profiler = pprofile.StatisticalProfile()
# statistical_profiler_thread = pprofile.StatisticalThread(
#     profiler=profiler,
# )



# symbolic
LP  = [
    ["p", "q"],
    ["p", "not-q"],
    ["not-p"],
]


# ?? dont know where computed
CP  = [
    ["c1", "c2", "c3"], #path1
    ["c4", "c5", "c6"], #path2 
    ["c7", "c8", "c9"], #path3
]


# concrte
LPprime  = [
    ["p", "r", "q"],
    ["p", "r", "not-q"],
    ["p", "not-r"],
    ["not-p"],
]


# concrete
CPprime  = [
    ["c4", "c5"], 
    ["c4", "c5"], 
    ["c6"],
    ["c7"],
]

def main():
    num_P = 3
    num_Pprime = 4

    assert(num_P == len(LP))
    assert(num_P == len(CP))
    assert(num_Pprime == len(LPprime))
    assert(num_Pprime == len(CPprime))

    option_in = True

    all_constraints = []

    for pi in range(num_P):
        
        for piprime in range(num_Pprime):
            
            # option 1
            PLiterals = LP[pi] + CP[pi] 
            # PLiterals = LP(pi)
            
            
            # Options 2
            # PprimeLiterals = LPprime[piprime] + CPprime[piprime] 
            PprimeLiterals = LPprime(piprime)
            
            
            # SET CONTRAINTS
            set_cons = "" 
            for l in PLiterals:
                
                #option 3
                l = l
                # l = "( not " + l + ")"
                
                # option 4
                if option_in:
                    set_cons +=  '\t\t(or ' + ' '.join([  "(= " + l + " " + lit + ")"  for lit in  PprimeLiterals]) + ')\n'
                

                # elif not option_in:
                #     set_cons += '\t\t(and ' + ' '.join([  "(not (= " + l + " " + lit + "))"  for lit in  PprimeLiterals]) + ')\n'
                
            set_cons = "\t(and \n" + set_cons + "\t)\n"
            
            
            # IMP CONSTRAINTS
            # CPprint(piprime) subset CP[pi] 
            
            imp_cons = ""
            matchcl = []
            
            for clprime in CPprime[piprime]:
                imp_cons += "\t\t(or "  + ' '.join(["(= " + clprime + " " + cl +" )"  for cl in CP[pi] ]) + ")\n"
                
            imp_cons =  "\n\t(and \n" + imp_cons + "\t)\n"
            
            # print(imp_cons)
            final_constraint = '( => \n' + set_cons  + imp_cons + ")\n" 
            
            all_constraints.append(final_constraint)
            
            
    constraints = "\n(and\n\n" + "\n".join(all_constraints) + "\n)"

    print(constraints.expandtabs(4))



# cProfile.run('main()')

with profiler:
# with statistical_profiler_thread:
    main()
    
profiler.print_stats()
