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


// N-QUEENS PUZZLE
//
// Before moving onto harder and more interesting problems, let's exercise the
// SAT solver and the constraint definitions together by solving the N-queens
// puzzle. The definition is simple: assign a single variable to "is there a
// queen on this square?" for each square of the board, and then make sure that
// there's at least one queen in each row, and at most one queen in each column
// and diagonal.

function pretty(solution) {
  const n = solution.length;
  const k = Math.sqrt(n);
  if(!Number.isInteger(k)) { throw new Error("Invalid board size"); }

  const squares = [];
  for(let i = 0; i < n; i++) {
    const l = solution[i];
    if(l < 0) { continue; }

    const v = Math.abs(l) - 1;
    const x = (v % k) + 1;
    const y = Math.floor(v / k) + 1;
    squares.push(String.fromCharCode(96 + x) + y);
  }

  return squares.sort().join(" ");
}

assert_equal(
  solve([
    ...at_least(1, [1, 2, 3, 4]),
    ...at_least(1, [5, 6, 7, 8]),
    ...at_least(1, [9, 10, 11, 12]),
    ...at_least(1, [13, 14, 15, 16]),
    ...at_most(1, [1, 5, 9, 13]),
    ...at_most(1, [2, 6, 10, 14]),
    ...at_most(1, [3, 7, 11, 15]),
    ...at_most(1, [4, 8, 12, 16]),
    ...at_most(1, [1]),
    ...at_most(1, [2, 5]),
    ...at_most(1, [3, 6, 9]),
    ...at_most(1, [4, 7, 10, 13]),
    ...at_most(1, [8, 11, 14]),
    ...at_most(1, [12, 15]),
    ...at_most(1, [16]),
    ...at_most(1, [13]),
    ...at_most(1, [9, 14]),
    ...at_most(1, [5, 10, 15]),
    ...at_most(1, [1, 6, 11, 16]),
    ...at_most(1, [2, 7, 12]),
    ...at_most(1, [3, 8]),
    ...at_most(1, [4]),
  ]).map(pretty),
  ["a3 b1 c4 d2", "a2 b4 c1 d3"],
  "Should solve the 4-Queens puzzle.",
);

assert_equal(
  solve([
    ...at_least(1, [1, 2, 3, 4, 5, 6, 7, 8]),
    ...at_least(1, [9, 10, 11, 12, 13, 14, 15, 16]),
    ...at_least(1, [17, 18, 19, 20, 21, 22, 23, 24]),
    ...at_least(1, [25, 26, 27, 28, 29, 30, 31, 32]),
    ...at_least(1, [33, 34, 35, 36, 37, 38, 39, 40]),
    ...at_least(1, [41, 42, 43, 44, 45, 46, 47, 48]),
    ...at_least(1, [49, 50, 51, 52, 53, 54, 55, 56]),
    ...at_least(1, [57, 58, 59, 60, 61, 62, 63, 64]),
    ...at_most(1, [1, 9, 17, 25, 33, 41, 49, 57]),
    ...at_most(1, [2, 10, 18, 26, 34, 42, 50, 58]),
    ...at_most(1, [3, 11, 19, 27, 35, 43, 51, 59]),
    ...at_most(1, [4, 12, 20, 28, 36, 44, 52, 60]),
    ...at_most(1, [5, 13, 21, 29, 37, 45, 53, 61]),
    ...at_most(1, [6, 14, 22, 30, 38, 46, 54, 62]),
    ...at_most(1, [7, 15, 23, 31, 39, 47, 55, 63]),
    ...at_most(1, [8, 16, 24, 32, 40, 48, 56, 64]),
    ...at_most(1, [1]),
    ...at_most(1, [2, 9]),
    ...at_most(1, [3, 10, 17]),
    ...at_most(1, [4, 11, 18, 25]),
    ...at_most(1, [5, 12, 19, 26, 33]),
    ...at_most(1, [6, 13, 20, 27, 34, 41]),
    ...at_most(1, [7, 14, 21, 28, 35, 42, 49]),
    ...at_most(1, [8, 15, 22, 29, 36, 43, 50, 57]),
    ...at_most(1, [16, 23, 30, 37, 44, 51, 58]),
    ...at_most(1, [24, 31, 38, 45, 52, 59]),
    ...at_most(1, [32, 39, 46, 53, 60]),
    ...at_most(1, [40, 47, 54, 61]),
    ...at_most(1, [48, 55, 62]),
    ...at_most(1, [56, 63]),
    ...at_most(1, [64]),
    ...at_most(1, [57]),
    ...at_most(1, [49, 58]),
    ...at_most(1, [41, 50, 59]),
    ...at_most(1, [33, 42, 51, 60]),
    ...at_most(1, [25, 34, 43, 52, 61]),
    ...at_most(1, [17, 26, 35, 44, 53, 62]),
    ...at_most(1, [9, 18, 27, 36, 45, 54, 63]),
    ...at_most(1, [1, 10, 19, 28, 37, 46, 55, 64]),
    ...at_most(1, [2, 11, 20, 29, 38, 47, 56]),
    ...at_most(1, [3, 12, 21, 30, 39, 48]),
    ...at_most(1, [4, 13, 22, 31, 40]),
    ...at_most(1, [5, 14, 23, 32]),
    ...at_most(1, [6, 15, 24]),
    ...at_most(1, [7, 16]),
    ...at_most(1, [8]),
  ]).map(pretty),
  [
    "a1 b7 c5 d8 e2 f4 g6 h3", "a1 b7 c4 d6 e8 f2 g5 h3",
    "a1 b6 c8 d3 e7 f4 g2 h5", "a1 b5 c8 d6 e3 f7 g2 h4",
    "a6 b1 c5 d2 e8 f3 g7 h4", "a4 b1 c5 d8 e2 f7 g3 h6",
    "a5 b1 c8 d4 e2 f7 g3 h6", "a3 b1 c7 d5 e8 f2 g4 h6",
    "a5 b1 c4 d6 e8 f2 g7 h3", "a7 b1 c3 d8 e6 f4 g2 h5",
    "a5 b1 c8 d6 e3 f7 g2 h4", "a4 b1 c5 d8 e6 f3 g7 h2",
    "a2 b6 c1 d7 e4 f8 g3 h5", "a5 b3 c1 d7 e2 f8 g6 h4",
    "a8 b3 c1 d6 e2 f5 g7 h4", "a4 b6 c1 d5 e2 f8 g3 h7",
    "a5 b7 c1 d4 e2 f8 g6 h3", "a6 b3 c1 d8 e4 f2 g7 h5",
    "a5 b3 c1 d6 e8 f2 g4 h7", "a6 b3 c1 d8 e5 f2 g4 h7",
    "a4 b8 c1 d3 e6 f2 g7 h5", "a8 b4 c1 d3 e6 f2 g7 h5",
    "a4 b8 c1 d5 e7 f2 g6 h3", "a4 b7 c1 d8 e5 f2 g6 h3",
    "a6 b4 c1 d5 e8 f2 g7 h3", "a6 b3 c1 d7 e5 f8 g2 h4",
    "a7 b3 c1 d6 e8 f5 g2 h4", "a5 b7 c1 d3 e8 f6 g4 h2",
    "a2 b5 c7 d1 e3 f8 g6 h4", "a2 b8 c6 d1 e3 f5 g7 h4",
    "a6 b2 c7 d1 e3 f5 g8 h4", "a7 b2 c4 d1 e8 f5 g3 h6",
    "a8 b2 c4 d1 e7 f5 g3 h6", "a5 b2 c8 d1 e4 f7 g3 h6",
    "a6 b2 c7 d1 e4 f8 g5 h3", "a5 b2 c6 d1 e7 f4 g8 h3",
    "a3 b5 c7 d1 e4 f2 g8 h6", "a6 b4 c7 d1 e8 f2 g5 h3",
    "a5 b8 c4 d1 e7 f2 g6 h3", "a3 b6 c8 d1 e5 f7 g2 h4",
    "a7 b5 c3 d1 e6 f8 g2 h4", "a6 b4 c7 d1 e3 f5 g2 h8",
    "a5 b8 c4 d1 e3 f6 g2 h7", "a3 b6 c4 d1 e8 f5 g7 h2",
    "a3 b6 c8 d1 e4 f7 g5 h2", "a5 b7 c4 d1 e3 f8 g6 h2",
    "a2 b6 c8 d3 e1 f4 g7 h5", "a2 b5 c7 d4 e1 f8 g6 h3",
    "a2 b7 c5 d8 e1 f4 g6 h3", "a7 b2 c6 d3 e1 f4 g8 h5",
    "a8 b2 c5 d3 e1 f7 g4 h6", "a4 b2 c8 d6 e1 f3 g5 h7",
    "a4 b2 c7 d5 e1 f8 g6 h3", "a3 b6 c2 d7 e1 f4 g8 h5",
    "a3 b5 c2 d8 e1 f7 g4 h6", "a6 b8 c2 d4 e1 f7 g5 h3",
    "a3 b8 c4 d7 e1 f6 g2 h5", "a3 b5 c8 d4 e1 f7 g2 h6",
    "a6 b3 c7 d4 e1 f8 g2 h5", "a6 b3 c5 d7 e1 f4 g2 h8",
    "a6 b3 c5 d8 e1 f4 g2 h7", "a4 b8 c5 d3 e1 f7 g2 h6",
    "a4 b7 c5 d3 e1 f6 g8 h2", "a4 b6 c8 d3 e1 f7 g5 h2",
    "a2 b4 c6 d8 e3 f1 g7 h5", "a4 b2 c5 d8 e6 f1 g3 h7",
    "a4 b2 c8 d5 e7 f1 g3 h6", "a3 b7 c2 d8 e5 f1 g4 h6",
    "a3 b6 c2 d5 e8 f1 g7 h4", "a3 b6 c2 d7 e5 f1 g8 h4",
    "a5 b7 c2 d6 e3 f1 g4 h8", "a5 b7 c2 d6 e3 f1 g8 h4",
    "a7 b4 c2 d5 e8 f1 g3 h6", "a7 b4 c2 d8 e6 f1 g3 h5",
    "a5 b7 c2 d4 e8 f1 g3 h6", "a3 b6 c8 d2 e4 f1 g7 h5",
    "a7 b3 c8 d2 e5 f1 g6 h4", "a4 b7 c5 d2 e6 f1 g3 h8",
    "a4 b6 c8 d2 e7 f1 g3 h5", "a5 b3 c8 d4 e7 f1 g6 h2",
    "a2 b7 c3 d6 e8 f5 g1 h4", "a4 b2 c7 d3 e6 f8 g1 h5",
    "a5 b2 c4 d6 e8 f3 g1 h7", "a3 b7 c2 d8 e6 f4 g1 h5",
    "a6 b4 c2 d8 e5 f7 g1 h3", "a6 b3 c7 d2 e4 f8 g1 h5",
    "a6 b3 c7 d2 e8 f5 g1 h4", "a4 b7 c3 d8 e2 f5 g1 h6",
    "a4 b2 c7 d3 e6 f8 g5 h1", "a5 b2 c4 d7 e3 f8 g6 h1",
    "a3 b5 c2 d8 e6 f4 g7 h1", "a3 b6 c4 d2 e8 f5 g7 h1",
  ],
  "Should solve the 8-Queens puzzle.",
);
