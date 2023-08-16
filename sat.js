// ASSERTIONS

function assert(test, message, Constructor=Error) {
  if(!test) { throw new Error(message); }
}

function validate(test, message) {
  assert(test, message, RangeError);
}

function test(actual, expected, message) {
  actual = JSON.stringify(actual);
  expected = JSON.stringify(expected);
  assert(actual === expected, `${message} (${actual} != ${expected})`);
}


// SAT SOLVING

// Next, we're going to want to validate the input in order to prevent any
// funny business from going on.

function validate_literal(literal) {
  validate(
    Number.isInteger(literal) && literal !== 0,
    "Expected a literal to be a positive or negative integer",
  );
}

function validate_clause(clause) {
  validate(Array.isArray(clause), "Expected a clause to be an Array");
  clause.forEach(validate_literal);
}

function validate_formula(formula) {
  validate(Array.isArray(formula), "Expected a formula to be an Array");
  formula.forEach(validate_clause);
}


function is_empty(array) {
  return array.length === 0;
}

function is_unit(array) {
  return array.length === 1;
}


function adjacent(formula) {
  const adjacent = [];
  const n = formula.length;

  for(let i = 0; i < n; i++) {
    const clause = formula[i];
    const m = clause.length;

    for(let j = 0; j < m; j++) {
      const variable = Math.abs(clause[j]);

      while(adjacent.length < variable) { adjacent.push([]); }
      adjacent[variable - 1].push(i);
    }
  }

  return adjacent;
}

function unit(formula) {
  const open = [];

  for(const clause of formula) {
    if(clause.length === 1) {
      open.push(clause[0]);
    }
  }

  return open;
}


function simplify(clause, literal) {
  const simplified = [];
  for(const candidate of clause) {
    if(candidate === literal) { return null; }
    if(candidate !== -literal) { simplified.push(candidate); }
  }

  return simplified;
}

// Apply unit propagation, returning true if we were able to do so successfully
// and false if we ran into a contradiction. This function will modify formula
// in-place. If it succeeds, open will be left empty; if not, open's state
// will be undefined (e.g. you will want to clear it before using it again).
// Closed will be appended to.
function unit_propagate(formula, adjacent, open, closed) {
  while(open.length !== 0) {
    const literal = open.shift();

    // FIXME: THIS IS LUDICROUSLY INEFFICIENT. How to ensure that this can't
    // happen in O(1) time?
    if(closed.includes(literal)) { continue; }

    closed.push(literal);

    for(const j of adjacent[Math.abs(literal) - 1]) {
      const clause = formula[j];
      if(clause === null) { continue; }

      const simplified = simplify(clause, literal);
      if(simplified !== null) {
        if(is_empty(simplified)) { open.length = 0; return false; }
        if(is_unit(simplified)) { open.push(simplified[0]); }
      }

      formula[j] = simplified;
    }
  }

  return true;
}

function is_defined(clause) {
  return clause !== null;
}

function sat_recursive(formula, adjacent, open, closed) {
  // Both steps of this function will modify formula, so we make a copy of it
  // to prevent any external harm.
  formula = formula.slice();

  for(;;) {
    // Apply unit propagation. If doing so turns up a contradiction, then bail.
    if(!unit_propagate(formula, adjacent, open, closed)) { return false; }

    // Check if any clauses are still present in the formula. (These will be
    // non-unit clauses.) If not, we're done, hooray! If there are, though,
    // then make a guess and recursively see if that gets us anywhere.
    const clause = formula.find(is_defined);
    if(clause === undefined) { break; }

    // Remember what we're sure of so far, so if our guess is wrong, we can
    // restore our state.
    const closed_length = closed.length;

    // Guess that the first literal remaining is true. If that works, yay!
    open.push(clause[0]);
    if(sat_recursive(formula, adjacent, open, closed)) { break; }

    // If not, rats. At least we know it's false now! Clean up our state and
    // then continue (in the current stack frame).
    open.length = 0;
    closed.length = closed_length;

    open.push(-clause[0]);
  }

  return true;
}


function by_variable_ascending(a, b) {
  return Math.abs(a) - Math.abs(b);
}

function sat(formula) {
  // Validate the input.
  validate_formula(formula);

  // Handle trivial special cases.
  if(is_empty(formula)) { return []; }
  if(formula.some(is_empty)) { return null; }

  // Find the formula's adjacency matrix and unit clauses, and then hand the
  // solving of the formula off to a recursive helper function. If it finds a
  // solution, make sure the variables are sorted before returning.
  const closed = [];
  if(sat_recursive(formula, adjacent(formula), unit(formula), closed)) {
    return closed.sort(by_variable_ascending);
  }

  // If it didn't find a solution... rats.
  return null;
}


// To make sure the SAT solver works, let's throw some sample problems at it.
// Each of these is taken from Knuth, TAOCP vol. 4 fasc. 6 "Satisfiability".

test(
  sat([[1, 2], [-1, 3], [-3, 4], [1]]),
  [1, 3, 4],
  "Should solve a simple 2SAT formula.",
);

test(
  sat([
    [1, 2, -3], [2, 3, -4], [1, 3, 4], [-1, 2, 4],
    [-1, -2, 3], [-2, -3, 4], [-3, -4, -1], [1, -2, -4],
  ]),
  null,
  "Should fail to solve \"the shortest interesting formula in 3CNF.\"",
);

test(
  sat([
    [1, 2, 3], [-1, -2, -3], [1, 3, 5], [-1, -3, -5],
    [1, 4, 7], [-1, -4, -7], [2, 3, 4], [-2, -3, -4],
    [2, 4, 6], [-2, -4, -6], [2, 5, 8], [-2, -5, -8],
    [3, 4, 5], [-3, -4, -5], [3, 5, 7], [-3, -5, -7],
    [4, 5, 6], [-4, -5, -6], [4, 6, 8], [-4, -6, -8],
    [5, 6, 7], [-5, -6, -7], [6, 7, 8], [-6, -7, -8],
  ]),
  [1,-2,-3,4,5,-6,-7,8],
  "Should solve the van der Waerden sample problem proposed by Knuth.",
);


// CONSTRAINTS
//
// It can be tricky to write CNF clauses by hand, so we define ourselves some
// helper functions: at_most(), at_least(), and exactly(); these allow us to
// say that we want some number of a set of variables to be true.
//
// There are lots of ways to encode these constraints (see [1]). We use the
// simplest (and least efficient) of these (the "binomial" encoding) because
// we are only dealing with a very small problem domain, but it would be an
// interesting exercise to explore other encodings.
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

test(
  at_most(0, [1, 2, 3]),
  [[-1], [-2], [-3]],
  "at_most(0,Ls) should mean each L is false.",
);

test(
  at_most(1, [1, 2, 3]),
  [[-1, -2], [-1, -3], [-2, -3]],
  "at_most(1,Ls) should mean no two Ls are simultaneously true.",
);

test(
  at_most(2, [1, 2, 3]),
  [[-1, -2, -3]],
  "at_most(N-1,Ls) should mean some L is false.",
);

test(
  at_most(3, [1, 2, 3]),
  [],
  "at_most(N,Ls) means nothing.",
);

test(
  at_least(0, [1, 2, 3]),
  [],
  "at_least(0,Ls) means nothing.",
);

test(
  at_least(1, [1, 2, 3]),
  [[1, 2, 3]],
  "at_least(1,Ls) should mean some L is true.",
);

test(
  at_least(2, [1, 2, 3]),
  [[1, 2], [1, 3], [2, 3]],
  "at_least(N-1,Ls) should mean no two Ls are simultaneously false.",
);

test(
  at_least(3, [1, 2, 3]),
  [[1], [2], [3]],
  "at_least(N,Ls) should mean each L is true.",
);

// FIXME: Tests for exactly().


// N-QUEENS
//
// Before moving onto harder and more interesting problems, let's exercise the
// SAT solver and the constraint definitions together by solving the N-queens
// puzzle. The definition is simple: assign a single variable to "is there a
// queen on this square?" for each square of the board, and then make sure that
// there's at least one queen in each row, and at most one queen in each column
// and diagonal.

// Let's try 4-Queens, first, since it's easy.
test(
  sat([
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
  ]),
  [
     -1,   2,  -3,  -4,
     -5,  -6,  -7,   8,
      9, -10, -11, -12,
    -13, -14,  15, -16,
  ],
  "Should solve the 4-Queens puzzle.",
);

// Great! Now let's see if we can solve the real thing.
test(
  sat([
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
  ]),
  [
      1,  -2,  -3,  -4,  -5,  -6,  -7,  -8,
     -9, -10, -11, -12,  13, -14, -15, -16,
    -17, -18, -19, -20, -21, -22, -23,  24,
    -25, -26, -27, -28, -29,  30, -31, -32,
    -33, -34,  35, -36, -37, -38, -39, -40,
    -41, -42, -43, -44, -45, -46,  47, -48,
    -49,  50, -51, -52, -53, -54, -55, -56,
    -57, -58, -59,  60, -61, -62, -63, -64,
  ],
  "Should solve the 8-Queens puzzle.",
);
