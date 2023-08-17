// ASSERTIONS
//
// Normally, one would test their software using an external toolkit. For a toy
// like this, though, I'll just be inlining the tests as I go. For that, I'll
// need to be able to make simple assertions.

function assert(test, message) {
  if(!test) { throw new Error(message); }
}

function assert_equal(actual, expected, message) {
  // HACK: JSON.stringify() is, in fact, a horrible way to test deep equality.
  // Good enough for government work [shrug emoji].
  assert(JSON.stringify(actual) === JSON.stringify(expected), message);
}

function assert_includes(actuals, expected, message) {
  for(const actual of actuals) {
    if(JSON.stringify(actual) === expected) {
      return;
    }
  }

  assert(false, message);
}


// BOOLEAN SATISFIABILITY PROBLEM
//
// The Boolean Satisfiability Problem (SAT) is the problem of solving a boolean
// formula in conjunctive normal form. It can be thought of as a very bizarre
// programming language, where one gives the computer a number of parameters
// and the constraints that act upon those parameters, and then asks the
// computer to find which values of the parameters satisfy those constraints.
//
// There are a number of ways to solve the problem. The main categories are
// recursive search on variables, recursive search on clauses, and stochastic
// search. This particular solver is of the first category, following [1], and
// was chosen for simplicity rather than speed. (I expect it to be several
// orders of magnitude slower production solvers.) Nonetheless, I have made
// basic optimizations in order to keep it from being TOO stupid.
//
// The tests come from Knuth, The Art of Computer Programming, vol. 4 fasc. 6
// "Satisfiability."
//
// [1]: https://web.archive.org/web/20201109101535/http://www.cse.chalmers.se/~algehed/blogpostsHTML/SAT.html

function simplify_clause(clause, literal) {
  const n = clause.length;

  for(let i = 0; i < n; i++) {
    const l = clause[i];
    if(l === literal) { return null; }
    if(l !== -literal) { continue; }

    clause = clause.slice();
    let j = i++;

    for(; i < n; i++) {
      const l = clause[i];
      if(l === literal) { return null; }
      if(l !== -literal) { clause[j++] = l; }
    }

    clause.length = j;
    break;
  }

  return clause;
}

// NB: Unlike simplify_clause(), simplify_formula() always makes a copy of
// the original formula. This is simply because it is only ever called with
// literals that are known to be in it, so it will always be modified.
function simplify_formula(formula, literal) {
  const n = formula.length;
  const f = new Array(n);
  let j = 0;

  for(let i = 0; i < n; i++) {
    const c = simplify_clause(formula[i], literal);
    if(c === null) { continue; }
    if(c.length === 0) { return null; }

    f[j++] = c;
  }

  f.length = j;
  return f;
}

function prepend(solutions, literal) {
  const n = solutions.length;
  for(let i = 0; i < n; i++) {
    solutions[i].unshift(literal);
  }

  return solutions;
}

function solve(formula) {
  if(formula === null) { return []; }
  if(formula.length === 0) { return [[]]; }

  const l = formula[0][0];
  return prepend(solve(simplify_formula(formula, l)), l).
    concat(prepend(solve(simplify_formula(formula, -l)), -l));
}

assert_equal(
  solve([[1, 2], [-1, 3], [-3, 4], [1]]),
  [[1, 3, 4]],
  "Should solve a simple 2SAT formula.",
);

assert_equal(
  solve([
    [1, 2, -3], [2, 3, -4], [1, 3, 4], [-1, 2, 4],
    [-1, -2, 3], [-2, -3, 4], [-3, -4, -1], [1, -2, -4],
  ]),
  [],
  "Should fail to solve \"the shortest interesting formula in 3CNF.\"",
);

assert_equal(
  solve([
    [1, 2, 3], [-1, -2, -3], [1, 3, 5], [-1, -3, -5],
    [1, 4, 7], [-1, -4, -7], [2, 3, 4], [-2, -3, -4],
    [2, 4, 6], [-2, -4, -6], [2, 5, 8], [-2, -5, -8],
    [3, 4, 5], [-3, -4, -5], [3, 5, 7], [-3, -5, -7],
    [4, 5, 6], [-4, -5, -6], [4, 6, 8], [-4, -6, -8],
    [5, 6, 7], [-5, -6, -7], [6, 7, 8], [-6, -7, -8],
  ]),
  // FIXME: This is gross. It would be better if these were in lexicographic
  // order.
  [
    [ 1, -2, -3,  4, -7,  5, -6,  8],
    [ 1, -2,  3, -5, -4,  6,  8, -7],
    [ 1,  2, -3, -4,  5, -8,  6, -7],
    [-1,  2,  3, -4,  7, -5,  6, -8],
    [-1,  2, -3,  5,  4, -6, -8,  7],
    [-1, -2,  3,  4, -5,  8, -6,  7],
  ],
  "Should solve the van der Waerden sample problem proposed by Knuth.",
);
