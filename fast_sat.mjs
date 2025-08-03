// "Deoptimization" of Knuth's Algorithm B (TAOCP 7.2.2.2), to make it simpler
// to understand. See also [1].
//
// [1]: https://smt.st/current_tree/solvers/SAT_WL/SAT_WL.py

function dup(a) { return Array.from(a); }
function dup2(a) { return Array.from(a, dup); }

function to_var(l) { return Math.abs(l); }
function to_idx(l) { return ((to_var(l) - 1) << 1) | (l >>> 31); }

function assign(watch, assignment, p) {
  assignment[to_var(p) - 1] = p;

  const clauses = watch[to_idx(-p)];
  while(clauses.length) {
    const clause = clauses[0];
    for(let i = 1; i < clause.length; i++) {
      const q = clause[i];
      // If Q is TBD or if it's assignment is true, we'll watch it, instead.
      if(to_var(q) > to_var(p) || assignment[to_var(q) - 1] * Math.sign(q) >= 0) {
        // Watch q, instead.
        clause[i] = clause[0];
        clause[0] = q;

        // Move the clause to q's watchlist.
        watch[to_idx(q)].unshift(clauses.shift());
        break;
      }
    }

    // Uh oh. We couldn't find a satisfying Q. UNSAT.
    return false;
  }

  return true;
}

function backtrack(formula, watch, assignment, depth, solutions) {
  if(depth >= assignment.length) { solutions.push(dup(assignment)); return; }

  let l = depth + 1;
  if(watch[to_idx(l)].length < 1 || watch[to_idx(-l)].length >= 1) { l = -l; }

  if(assign(watch, assignment,  l)) {
    backtrack(formula, watch, assignment, depth + 1, solutions);
  }
  if(assign(watch, assignment, -l)) {
    backtrack(formula, watch, assignment, depth + 1, solutions);
  }
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

console.log(
  solve([ 
    [ 1,  2, -3],
    [ 2,  3, -4],
    [ 3,  4,  1],
    [ 4, -1,  2],
    [-1, -2,  3], 
    [-2, -3,  4],
    [-3, -4, -1],
    // [-4, 1, -2], // uncommenting this line will make the problem UNSAT
  ]),
);
