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
  const n = formula.length;

  for(let i = 0; i < n; i++) {
    const clause = formula[i];
    if(is_unit(clause)) { open.push(i); }
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
    const i = open.shift();
    const clause = formula[i];
    if(clause === null) { continue; }

    formula[i] = null;

    const literal = clause[0];
    closed.push(literal);

    for(const j of adjacent[Math.abs(literal) - 1]) {
      const clause = formula[j];
      if(clause === null) { continue; }

      const simplified = simplify(clause, literal);
      if(simplified !== null) {
        if(is_empty(simplified)) { open.length = 0; return false; }
        if(is_unit(simplified)) { open.push(j); }
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
    const i = formula.findIndex(is_defined);
    if(i === -1) { break; }

    // Remember what we're sure of so far, so if our guess is wrong, we can
    // restore our state.
    const formula_length = formula.length;
    const closed_length = closed.length;

    // Guess that the first literal remaining is true. If that works, yay!
    formula.push([formula[i][0]]);
    open.push(formula_length);
    if(sat_recursive(formula, adjacent, open, closed)) { break; }

    // If not, rats. At least we know it's false now! Clean up our state and
    // then continue (in the current stack frame).
    formula[formula_length][0] *= -1;
    open.length = 1;
    open[0] = formula_length;
    closed.length = closed_length;
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
  return [...at_most(k, literals), ...at_least(k, literals)];
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


// ADVANCED DUNGEONS AND DIAGRAMS
//
// AD&D[1] is a cute little pen-and-paper puzzle game by Zach Barth. I enjoyed
// it when I saw it, and later on a digital version was released as a part of
// the video game Last Call BBS[2]. I enjoyed solving all these puzzles too,
// but after beating all the puzzles in the game, you unlock an "infinite
// dungeon" that randomly generates new puzzles for you. How could I possibly
// beat an infinite number of puzzles? By writing a computer program to solve
// them for me, of course. But why stop at AD&D puzzles? Why not solve ANY
// puzzle? And that's why this little piece of software exists.
//
// [1]: https://trashworldnews.com/files/advanced_dungeons_and_diagrams.pdf
// [2]: https://www.zachtronics.com/last-call-bbs/

// Parse a string digit ("7") into a number (7)
function digit(c) {
  return c.charCodeAt(0) - 48;
}

// Enumerate `n` numbers starting at `start` and incrementing by `step`
function enumerate(n, start, step) {
  const ns = new Array(n);
  for(let i = 0; i < n; i++, start += step) { ns[i] = start; }

  return ns;
}

// Positive numbers are printed as walls, negative numbers as spaces.
function print(variable) {
  return (variable >= 0)? "#": " ";
}

// Parse and solve an Advanced Dungeons and Diagrams puzzle.
function dungeons_and_diagrams(input) {
  // Parse diagram input
  const match = /^ *(.+)\n+ *([0-8]{8})\n *([0-8])([ MT]{0,8})\n *([0-8])([ MT]{0,8})\n *([0-8])([ MT]{0,8})\n *([0-8])([ MT]{0,8})\n *([0-8])([ MT]{0,8})\n *([0-8])([ MT]{0,8})\n *([0-8])([ MT]{0,8})\n *([0-8])([ MT]{0,8})$/gm.exec(input);
  if(match === null) throw new RangeError("Input wasn't in diagram format");

  const name = match[1];
  const cols = Array.from(match[2], digit);
  const rows = [
    digit(match[3]), digit(match[5]), digit(match[7]), digit(match[9]),
    digit(match[11]), digit(match[13]), digit(match[15]), digit(match[17]),
  ];
  const monsters = [];
  const treasures = [];
  for(let y = 0; y < 8; y++) {
    const row = match[4 + y * 2];
    for(let x = 0; x < row.length; x++) {
      switch(row.charCodeAt(x)) {
        case 77: monsters.push([x, y]); break;
        case 84: treasures.push([x, y]); break;
      }
    }
  }

  // FIXME: Support treasures, too.
  if(treasures.length !== 0) {
    console.warn("Didn't attempt to solve %s", name);
    return;
  }

  // Convert to CNF.
  const formula = [];

  // There should be exactly N filled squares per column and row.
  for(let i = 0; i < 8; i++) {
    formula.push(...exactly(cols[i], enumerate(8, i + 1, 8)));
    formula.push(...exactly(rows[i], enumerate(8, i * 8 + 1, 1)));
  }

  // There should be at least 1 wall in every 2x2 square.
  // FIXME: Unless we're in a treasure room!
  for(let y = 8; y < 64; y += 8) {
    for(let x = 1; x < 8; x++) {
      formula.push(...at_least(1, [y + x - 8, y + x - 7, y + x, y + x + 1]));
    }
  }

  // There are no walls where there are monsters or treasures.
  for(const [x, y] of [...monsters, ...treasures]) {
    formula.push([-(y * 8 + x + 1)]);
  }

  // Each monster should be in a dead end.
  for(const [x, y] of monsters) {
    const set = [];
    if(x >= 1) { set.push(y * 8 + x); }
    if(x <= 6) { set.push(y * 8 + x + 2); }
    if(y >= 1) { set.push(y * 8 + x + 7); }
    if(y <= 6) { set.push(y * 8 + x + 9); }
    formula.push(...exactly(set.length - 1, set));
  }

  const assignment = sat(formula);
  if(assignment === null) {
    console.warn("Failed to solve %s", name);
    return;
  }

  const output = [
    assignment.slice( 0,  8).map(print),
    assignment.slice( 8, 16).map(print),
    assignment.slice(16, 24).map(print),
    assignment.slice(24, 32).map(print),
    assignment.slice(32, 40).map(print),
    assignment.slice(40, 48).map(print),
    assignment.slice(48, 56).map(print),
    assignment.slice(56, 64).map(print),
  ];
  for(const [x, y] of monsters) {
    output[y][x] = "M";
  }
  for(const [x, y] of treasures) {
    output[y][x] = "T";
  }

  console.log(
    "%s\n\n   %s\n  %s%s\n  %s%s\n  %s%s\n  %s%s\n  %s%s\n  %s%s\n  %s%s\n  %s%s\n",
    name,
    cols.join(""),
    rows[0], output[0].join(""),
    rows[1], output[1].join(""),
    rows[2], output[2].join(""),
    rows[3], output[3].join(""),
    rows[4], output[4].join(""),
    rows[5], output[5].join(""),
    rows[6], output[6].join(""),
    rows[7], output[7].join(""),
  );
}




dungeons_and_diagrams(`
  Tenaxxus's Gullet

   44262347
  7     M
  3
  4 T
  1
  7
  1M
  6
  3  M    M
`);

dungeons_and_diagrams(`
  The Twin Cities of the Dead

   13153435
  5
  2  T T
  2
  3
  6M
  0
  6
  1    M M
`);

dungeons_and_diagrams(`
  The Gardens of Hell

   14363144
  6M      M
  0
  4
  1       M
  5M
  3
  3    T
  4M
`);

dungeons_and_diagrams(`
  The House Penumbral

   04073432
  6M M
  2       T
  3
  1
  5
  1
  4
  1      M
`);

dungeons_and_diagrams(`
  The Maze of the Minotaur

   72613261
  0M
  7
  3 M T
  3
  3
  5
  2
  5
`);

dungeons_and_diagrams(`
  The Halls of the Golemancer

   53246415
  6     M
  3       M
  3  T  M
  3       M
  5     M
  3       M
  4
  3
`);

dungeons_and_diagrams(`
  The Tomb of the Broken God

   13326241
  1 T  M
  4
  1
  6
  2       M
  2
  5
  1     M
`);

dungeons_and_diagrams(`
  The Hive of Great Sorrow

   36054063
  6  M  M
  2M      M
  4
  3    M
  2
  4
  2M      M
  4
`);

dungeons_and_diagrams(`
  The Lair of the Elemental King

   52125423
  4       M
  1
  4  M
  2
  6
  2
  3   T
  2
`);
