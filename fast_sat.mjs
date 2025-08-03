// "Deoptimization" of Knuth's Algorithm B (TAOCP 7.2.2.2), to make it simpler
// to understand. See also [1].
//
// [1]: https://smt.st/current_tree/solvers/SAT_WL/SAT_WL.py

function dup(a) { return Array.from(a); }
function dup2(a) { return Array.from(a, dup); }

function to_var(l) { return Math.abs(l); }
function to_idx(l) { return ((to_var(l) - 1) << 1) | (l >>> 31); }

function backtrack(formula, watch, assignment, v, solutions) {
  if(v >= assignment.length) { solutions.push(dup(assignment)); return; }

  // FIXME
}

function solve(formula) {
  // Validate input and count variables.
  let n = 0;

  if(!Array.isArray(formula)) { throw new TypeError("Invalid formula"); }

  for(const clause of formula) {
    if(!Array.isArray(clause)) { throw new TypeError("Invalid clause"); }
    if(!clause.length) { return []; } // UNSAT

    for(const literal of clause) {
      if(!Number.isInteger(literal)) { throw new TypeError("Invalid literal"); }

      const v = to_var(literal);
      if(!(v >= 1 && v < 2147483649)) { throw new RangeError("Invalid variable"); }

      if(v > n) { n = v; }
    }
  }

  // Deep copy formula since we'll be modifying it.
  formula = dup2(formula);

  // Make our watch lists.
  const watch = new Array(n * 2);
  for(let i = 0; i < watch.length; i++) { watch[i] = []; }
  for(const clause of formula) { watch[to_idx(clause[0])].push(clause); }

  // Backtracking search.
  const assignment = new Array(n).fill(0);
  const solutions = [];
  backtrack(formula, watch, assignment, 0, solutions);
  return solutions;
}

solve([ 
  [ 1,  2, -3],
  [ 2,  3, -4],
  [ 3,  4,  1],
  [ 4, -1,  2],
  [-1, -2,  3], 
  [-2, -3,  4],
  [-3, -4, -1],
  // [-4, 1, -2], // uncommenting this line will make the problem UNSAT
]);
