import sys
import copy

def is_all_unique(assignment, positions):
    """ assignment is dict of position:value, positions is a list of tuples"""
    return all(assignment[p1] != assignment[p2]
		    for p1 in positions
	 		  for p2 in positions if p1 != p2)

def row_to_indices(row):
    """Returns a list of positions in this row.
    A position is a tuple"""
    return [(row, col) for col in range(0, 9)]

def col_to_indices(col):
    """Returns a list of positions in this column.
    A position is a tuple"""
    return [(row, col) for row in range(0, 9)]

def box_to_indices(box):
    """Returns a list of positions in this box.
    A position is a tuple"""
    start_row = (box // 3) * 3
    start_col = (box % 3) * 3
    return [(row, col) for row in range(start_row, start_row + 3)
                       for col in range(start_col, start_col + 3)]
	
class Constraint(object):
    """A Constraint consists of
    * scope: is a list of tuples. A tuple represents a position in the grid
    * condition: a function that can be applied to a tuple of values for
    the variable
    """
    def __init__(self, scope, condition):
        self.scope = scope
        self.condition = condition
  
    def holds(self, assignment):
        """
        precondition: all variables are assigned in assignment
        """
        return self.condition(assignment, self.scope)
    
class CSP(object):
    """
    A CSP consists of
    * domains, a dictionary that maps each variable to its domain
    * constraints, a list of constraints
    * variables, a set of variables. A variable is a tuple (row, col)
    * var_to_const, a variable to set of constraints dictionary
    (the arc linking a variable to its constraint)
    """
    def __init__(self, domains, constraints):
        """
        domains is a variable:domain dictionary.
        constraints is a list of constraints.
        """
        self.variables = set(domains) # Retrieves the key set.
        self.domains = domains
        self.constraints = constraints
        self.var_to_const = dict([var, set()] for var in self.variables) # dict comprehension not introduced in python <= 2.6
        for con in constraints:
            for var in con.scope:
                self.var_to_const[var].add(con)
    
    def consistent(self, puzzle):
        """
        assignment is a variable:value dictionary
        returns True if all of the constraints that can be 
        evaluated evaluate to True given assignment.
        """
        return all(con.holds(puzzle, con.scope) for con in self.constraints)
      
class Solver:
    """ Solve by first making csp arc-consistent."""
    def __init__(self, csp):
        self.csp = csp

    #call this 'arc'
    def new_to_do(self, var, const):
        """
        returns a set of arcs, (nvar, nconst), where nvar is neighbour of var
        and nconst is another constraint of var.
        """
        return set((nvar, nconst) for nconst in self.csp.var_to_const[var]
                if nconst != const
                for nvar in nconst.scope
                if nvar != var)
            
    def make_arc_consistent(self, orig_domains=None, to_do=None):
        if orig_domains is None:
            orig_domains = self.csp.domains

        if to_do is None:
            to_do = set((var, const) for const in self.csp.constraints for var in const.scope)
        else:
            to_do = to_do.copy()
        domains = orig_domains.copy()
        while to_do:
            var, const = self.select_arc(to_do)
            other_vars = [ov for ov in const.scope if ov != var]
            # Perform Revise(domain). O(d^n) for n-ary CSP
            new_domain = set(val for val in domains[var] if self.any_holds(domains, const, dict([[var,val]]), other_vars))
            if new_domain != domains[var]:
                domains[var] = new_domain
                add_to_do = self.new_to_do(var, const) - to_do # new todos not already inside
                to_do = to_do | add_to_do # set union
        return domains
		
    def select_arc(self, to_do):
        return to_do.pop()
        
    # O(d^n-1) for n-ary CSP. Basically this methods try every combination
    # of values for other variables in the scope.
    def any_holds(self, domains, const, env, other_vars, ind=0, assigned_vars=[]):
        """
        returns True if Constraint const holds for an assignment
        that extends env with the variables in other_vars[ind:].
        env is a dictionary
        Warning: this has side effects and changes the elements of env
        """
        # All the variables in the scope of the constraints has been assigned.
        if ind == len(other_vars): 
            return const.holds(env)
        else:
            var = other_vars[ind]
            for val in domains[var]:
                env[var] = val
                if is_all_unique(env, [var] + assigned_vars) and self.any_holds(domains, const, env, other_vars, ind + 1, [var] + assigned_vars):
                    return True
            return False
        
    # solve by domain-splitting -> keep attempting to make the csp arc-consistent after each splitting.
    def solve_recursive_ds(self, domains=None, to_do=None):
        """returns one solution (dict of var:val) or False if there are no solutions
        to_do is the list of CSP arcs to check
        """
        if domains is None:
            domains = self.csp.domains
        new_domains = self.make_arc_consistent(domains, to_do)
        if any(len(new_domains[var]) == 0 for var in domains):
            return False
        elif all(len(new_domains[var]) == 1 for var in domains):
            return dict((var, self.select_first(new_domains[var])) for var in domains) # solution - a dictionary of variable (tuple) as key, value (int) as value.
        else:
            var = self.select_most_constrained_var(x for x in self.csp.variables if len(new_domains[x]) > 1)
            if var:
                dom1, dom2 = self.partition_domain(new_domains[var])
                new_dom1 = self.copy_with_assign(new_domains, var, dom1)
                new_dom2 = self.copy_with_assign(new_domains, var, dom2)
                to_do = self.new_to_do(var, None)
                return self.solve_recursive_ds(new_dom1, to_do) or self.solve_recursive_ds(new_dom2, to_do)

    def select_var(self, iterables):
        """returns the next variable to split"""
        return self.select_first(iterables)
    
    def select_most_constrained_var(self, iterables):
        """returns the the variable with the most constrained domain"""
        return self.select_first([var for var in iterables if len(self.csp.domains[var]) == min(len(self.csp.domains[i]) for i in iterables)])
    
    def partition_domain(self, dom):
        """partitions domain dom into two."""
        split = len(dom) // 2
        dom1 = set(list(dom)[0:split])
        dom2 = dom - dom1
        return dom1, dom2

    def copy_with_assign(self, domains, var=None, new_domain=set()):
        """create a copy of the domains with an assignment var=new_domain
        if var==None then it is just a copy.
        """
        newdoms = domains.copy()
        if var is not None:
              newdoms[var] = new_domain
        return newdoms

    def select_first(self, iterables):
        for iterable in iterables:
            return iterable

class Sudoku(object):
    def __init__(self, puzzle):
        # you may add more attributes if you need
        self.puzzle = puzzle # self.puzzle is a list of lists
        self.ans = copy.deepcopy(puzzle) # self.ans is a list of lists
        self.domains = dict(((r,c),[x for x in range(1, 10)]) for r in range(0, len(self.puzzle)) for c in range(0, len(self.puzzle[r])))
        # Assigns knowns values to variables
        for i in range(0, len(self.puzzle)):
           for j in range(0, len(self.puzzle[i])):
               if self.puzzle[i][j] != 0:
                   self.domains[(i,j)] = [self.puzzle[i][j]] 
                
        self.constraints = [Constraint([(i, j) for j in range(0, 9)] , is_all_unique) for i in range(0, 9)] + [Constraint([(i, j) for i in range(0, 9)] , is_all_unique) for j in range(0, 9)] + [Constraint(box_to_indices(q), is_all_unique) for q in range(0, 9)] # constraints for the 9 boxes
        self.csp = CSP(self.domains, self.constraints)

    def solve(self):
        #TODO: Your code here
        solver = Solver(self.csp)
        solutions = solver.solve_recursive_ds() # or solve_recursive_ds()
        self.ans = [[0 for a in range(10)] for b in range(10)]
        for pos, val in solutions.items():
            self.ans[pos[0]][pos[1]] = val
        # don't print anything here. just return the answer
        # self.ans is a list of lists
        return self.ans

    # you may add more classes/functions if you think is useful
    # However, ensure all the classes/functions are in this file ONLY

if __name__ == "__main__":
    # STRICTLY do NOT modify the code in the main function here
    if len(sys.argv) != 3:
        print ("\nUsage: python sudoku_A2_xx.py input.txt output.txt\n")
        raise ValueError("Wrong number of arguments!")

    try:
        f = open(sys.argv[1], 'r')
    except IOError:
        print ("\nUsage: python sudoku_A2_xx.py input.txt output.txt\n")
        raise IOError("Input file not found!")

    puzzle = [[0 for i in range(9)] for j in range(9)]
    lines = f.readlines()

    i, j = 0, 0
    for line in lines:
        for number in line:
            if '0' <= number <= '9':
                puzzle[i][j] = int(number)
                j += 1
                if j == 9:
                    i += 1
                    j = 0

    sudoku = Sudoku(puzzle)
    ans = sudoku.solve()

    with open(sys.argv[2], 'a') as f:
        for i in range(9):
            for j in range(9):
                f.write(str(ans[i][j]) + " ")
            f.write("\n")
