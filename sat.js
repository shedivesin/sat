// First, lets add some simple assertions for making sure things work as we go.

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
    closed.push(literal);

    for(const j of adjacent[Math.abs(literal) - 1]) {
      const clause = formula[j];
      if(clause === null) { continue; }

      const simplified = simplify(clause, literal);
      if(simplified !== null) {
        if(is_empty(simplified)) { return false; }
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

function solve_sat_recursive(formula, adjacent, open, closed) {
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
    if(solve_sat_recursive(formula, adjacent, open, closed)) { break; }

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

function solve_sat(formula) {
  // Validate the input.
  validate_formula(formula);

  // Handle trivial special cases.
  if(is_empty(formula)) { return []; }
  if(formula.some(is_empty)) { return null; }

  // Find the formula's adjacency matrix and unit clauses, and then hand the
  // solving of the formula off to a recursive helper function. If it finds a
  // solution, make sure the variables are sorted before returning.
  const closed = [];
  if(solve_sat_recursive(formula, adjacent(formula), unit(formula), closed)) {
    return closed.sort(by_variable_ascending);
  }

  // If it didn't find a solution... rats.
  return null;
}


// To make sure the SAT solver works, let's throw some sample problems at it.
// Each of these is taken from Knuth, TAOCP vol. 4 fasc. 6 "Satisfiability".

test(
  solve_sat([[1, 2], [-1, 3], [-3, 4], [1]]),
  [1, 3, 4],
  "Should solve a simple 2SAT formula.",
);

test(
  solve_sat([
    [1, 2, -3], [2, 3, -4], [1, 3, 4], [-1, 2, 4],
    [-1, -2, 3], [-2, -3, 4], [-3, -4, -1], [1, -2, -4],
  ]),
  null,
  "Should fail to solve \"the shortest interesting formula in 3CNF.\"",
);

test(
  solve_sat([
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
