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


// BOOLEAN SATISFIABILITY PROBLEM
//
// The Boolean Satisfiability Problem (SAT) is the problem of solving a boolean
// formula in conjunctive normal form. It can be thought of as a very bizarre
// programming language, where one gives the computer a number of parameters
// and the constraints that act upon those parameters, and then asks the
// computer to find which values of the parameters satisfy those constraints.
// It turns out that this is a very natural way to express logic puzzles (among
// others).
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


// CONSTRAINT DEFINITION
//
// It can be tricky to write CNF clauses by hand, so we define ourselves some
// helper functions: at_most(), at_least(), and exactly(); these allow us to
// say that we want some number of a set of variables to be true.
//
// There are lots of ways to encode these constraints (see [1]). Since this is
// just a toy, we use the simplest (and least efficient) of these, called the
// "binomial" encoding. It would be an interesting exercise to explore some of
// the other encodings, though.
//
// [1]: https://www.it.uu.se/research/group/astra/ModRef10/papers/Alan%20M.%20Frisch%20and%20Paul%20A.%20Giannoros.%20SAT%20Encodings%20of%20the%20At-Most-k%20Constraint%20-%20ModRef%202010.pdf

function combinations(k, array, sign) {
  const n = array.length;
  if(!(k >= 1 & k <= n)) { return []; }

  const combinations = [];
  const c = new Array(k);
  c[0] = -1;

  for(let i = 0; c[0] !== n - k; ) {
    ++c[i];

    while(++i !== k) c[i] = c[i - 1] + 1;

    const combination = new Array(k);
    for(let j = 0; j < k; j++) combination[j] = array[c[j]] * sign;
    combinations.push(combination);

    while(c[--i] === n + i - k);
  }

  return combinations;
}

function at_most(k, literals) {
  return combinations(k + 1, literals, -1);
}

function at_least(k, literals) {
  return combinations(literals.length - k + 1, literals, 1);
}

function exactly(k, literals) {
  return at_most(k, literals).concat(at_least(k, literals));
}

assert_equal(
  at_most(0, [1, 2, 3]),
  [[-1], [-2], [-3]],
  "at_most(0,Ls) should mean each L is false.",
);

assert_equal(
  at_most(1, [1, 2, 3]),
  [[-1, -2], [-1, -3], [-2, -3]],
  "at_most(1,Ls) should mean no two Ls are simultaneously true.",
);

assert_equal(
  at_most(2, [1, 2, 3]),
  [[-1, -2, -3]],
  "at_most(N-1,Ls) should mean some L is false.",
);

assert_equal(
  at_most(3, [1, 2, 3]),
  [],
  "at_most(N,Ls) means nothing.",
);

assert_equal(
  at_least(0, [1, 2, 3]),
  [],
  "at_least(0,Ls) means nothing.",
);

assert_equal(
  at_least(1, [1, 2, 3]),
  [[1, 2, 3]],
  "at_least(1,Ls) should mean some L is true.",
);

assert_equal(
  at_least(2, [1, 2, 3]),
  [[1, 2], [1, 3], [2, 3]],
  "at_least(N-1,Ls) should mean no two Ls are simultaneously false.",
);

assert_equal(
  at_least(3, [1, 2, 3]),
  [[1], [2], [3]],
  "at_least(N,Ls) should mean each L is true.",
);

assert_equal(
  exactly(0, [1, 2, 3]),
  [[-1], [-2], [-3]],
  "exactly(0,Ls) should mean each L is false.",
);

assert_equal(
  exactly(1, [1, 2, 3]),
  [[-1, -2], [-1, -3], [-2, -3], [1, 2, 3]],
  "exactly(1,Ls) should mean some L is true but no two Ls are.",
);

assert_equal(
  exactly(2, [1, 2, 3]),
  [[-1, -2, -3], [1, 2], [1, 3], [2, 3]],
  "exactly(N-1,Ls) should mean some L is false but no two Ls are.",
);

assert_equal(
  exactly(3, [1, 2, 3]),
  [[1], [2], [3]],
  "exactly(N,Ls) should mean each L is true.",
);
