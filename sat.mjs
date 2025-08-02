import {deepStrictEqual as assert_equal} from "node:assert";


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

// If clause contains literal, the clause is satisfied: return null. Otherwise,
// return the clause with all instances of -literal removed. (As an
// optimization, if clause does not contain any instances of -literal, the
// original array is returned.)
function simplify_clause(clause, literal) {
  const n = clause.length;

  // If clause contains literal, return null. Also count how many times clause
  // contains -literal.
  let i = n;
  let j = 0;
  while(i) {
    const l = clause[--i];
    if(l ===  literal) { return null; }
    if(l === -literal) { ++j; }
  }

  // OPTIMIZATION: If clause contains -literal zero times, then just return it.
  // This prevents us from allocating a new array.
  if(!j) { return clause; }

  // Create and return a copy of clause with all instances of -literal removed.
  i = n;
  j = n - j;
  const simplified = new Array(j);
  while(i) {
    const l = clause[--i];
    if(l !== -literal) { simplified[--j] = l; }
  }

  return simplified;
}

// Return a copy of the formula with all clauses containing literal removed,
// and with all instances of -literal removed from their respective clauses.
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

// Prepend literal to every solution in a list of solutions. This modifies the
// input arrays, which is a little evil, but it's safe in this case since the
// input arrays (in solve()) are never used elsewhere.
function append(solutions, literal) {
  for(const solution of solutions) { solution.push(literal); }
  return solutions;
}

// Return EVERY POSSIBLE solution to the given CNF formula. (An empty array
// means there are no solutions and the formula is UNSAT.)
// NB: Be careful! There may be many!
function solve(formula) {
  // A null formula is one in which a contradiction has been found. (See
  // simplify_formula().) That's UNSAT, so return no solutions.
  if(formula === null) { return []; }

  // A formula with no clauses has a trivial solution.
  if(formula.length === 0) { return [[]]; }

  // Pick an arbitrary variable from the formula, and (recursively) try to
  // solve the formulas that result from assuming it to be either true or
  // false. If we find any solutions, simply prepend our assumptions to them.
  const l = formula[0][0];
  return append(solve(simplify_formula(formula, l)), l).
    concat(append(solve(simplify_formula(formula, -l)), -l));
}

function by_variable(a, b) {
  return Math.abs(a) - Math.abs(b);
}

function sort_by_variable(solutions) {
  for(const solution of solutions) { solution.sort(by_variable); }
  return solutions;
}

assert_equal(
  sort_by_variable(solve([[1, 2], [-1, 3], [-3, 4], [1]])),
  [[1, 3, 4]],
  "a simple 2SAT formula",
);

assert_equal(
  sort_by_variable(solve([
    [1, 2, -3], [2, 3, -4], [1, 3, 4], [-1, 2, 4],
    [-1, -2, 3], [-2, -3, 4], [-3, -4, -1], [1, -2, -4],
  ])),
  [],
  "the \"shortest interesting formula in 3CNF\"",
);

assert_equal(
  sort_by_variable(solve([
    [1, 2, 3], [-1, -2, -3], [1, 3, 5], [-1, -3, -5],
    [1, 4, 7], [-1, -4, -7], [2, 3, 4], [-2, -3, -4],
    [2, 4, 6], [-2, -4, -6], [2, 5, 8], [-2, -5, -8],
    [3, 4, 5], [-3, -4, -5], [3, 5, 7], [-3, -5, -7],
    [4, 5, 6], [-4, -5, -6], [4, 6, 8], [-4, -6, -8],
    [5, 6, 7], [-5, -6, -7], [6, 7, 8], [-6, -7, -8],
  ])),
  [
    [ 1, -2, -3,  4,  5, -6, -7,  8],
    [ 1, -2,  3, -4, -5,  6, -7,  8],
    [ 1,  2, -3, -4,  5,  6, -7, -8],
    [-1,  2,  3, -4, -5,  6,  7, -8],
    [-1,  2, -3,  4,  5, -6,  7, -8],
    [-1, -2,  3,  4, -5, -6,  7,  8],
  ],
  "Knuth's sample van der Waerden problem",
);


// N-QUEENS PUZZLE
//
// Before moving onto harder and more interesting problems, let's exercise the
// SAT solver by solving the N-queens puzzle. The definition is simple: assign
// a single variable to "is there a queen on this square?" for each square of
// the board, and then make sure that there's at least one queen in each row,
// and at most one queen in each column and diagonal.
function n_queens(n) {
  const formula = [];

  // There should be a queen in each row.
  for(let y = 0; y < n; y++) {
    const row = new Array(n);
    for(let x = 0; x < n; x++) {
      row[x] = y * n + x + 1;
    }

    formula.push(row);
  }

  // Each pair of squares in the same column or diagonal should have at least
  // one empty square.
  for(let x = 0; x < n; x++) {
    for(let y2 = 1; y2 < n; y2++) {
      for(let y1 = 0; y1 < y2; y1++) {
        formula.push([-(y1 * n + x + 1), -(y2 * n + x + 1)]);

        const x1 = x + y1 - y2;
        if(x1 >= 0) { formula.push([-(y1 * n + x + 1), -(y2 * n + x1 + 1)]); }

        const x2 = x + y2 - y1;
        if(x2 <  n) { formula.push([-(y1 * n + x + 1), -(y2 * n + x2 + 1)]); }
      }
    }
  }

  return formula;
}

function to_chess_notation(solution) {
  const n = solution.length;
  const k = Math.floor(Math.sqrt(n));
  if(!(k >= 1 && k < 27 && n === k * k)) { throw new Error("Invalid board size"); }

  const squares = [];
  for(let i = 0; i < n; i++) {
    const l = solution[i];
    if(!(l >= 1)) { continue; }

    const x = ((l - 1) % k);
    const y = Math.floor((l - 1) / k);
    if(!(x >= 0 && x < k && y >= 0 && y < k)) { continue; }

    squares.push(String.fromCharCode(97 + x) + (y + 1));
  }

  return squares.sort().join(" ");
}

console.time("4-Queens");
assert_equal(
  solve(n_queens(4)).map(to_chess_notation).sort(),
  ["a2 b4 c1 d3", "a3 b1 c4 d2"],
  "Should solve the 4-Queens puzzle.",
);
console.timeEnd("4-Queens");

console.time("8-Queens");
assert_equal(
  solve(n_queens(8)).map(to_chess_notation).sort(),
  [
    "a1 b5 c8 d6 e3 f7 g2 h4", "a1 b6 c8 d3 e7 f4 g2 h5",
    "a1 b7 c4 d6 e8 f2 g5 h3", "a1 b7 c5 d8 e2 f4 g6 h3",
    "a2 b4 c6 d8 e3 f1 g7 h5", "a2 b5 c7 d1 e3 f8 g6 h4",
    "a2 b5 c7 d4 e1 f8 g6 h3", "a2 b6 c1 d7 e4 f8 g3 h5",
    "a2 b6 c8 d3 e1 f4 g7 h5", "a2 b7 c3 d6 e8 f5 g1 h4",
    "a2 b7 c5 d8 e1 f4 g6 h3", "a2 b8 c6 d1 e3 f5 g7 h4",
    "a3 b1 c7 d5 e8 f2 g4 h6", "a3 b5 c2 d8 e1 f7 g4 h6",
    "a3 b5 c2 d8 e6 f4 g7 h1", "a3 b5 c7 d1 e4 f2 g8 h6",
    "a3 b5 c8 d4 e1 f7 g2 h6", "a3 b6 c2 d5 e8 f1 g7 h4",
    "a3 b6 c2 d7 e1 f4 g8 h5", "a3 b6 c2 d7 e5 f1 g8 h4",
    "a3 b6 c4 d1 e8 f5 g7 h2", "a3 b6 c4 d2 e8 f5 g7 h1",
    "a3 b6 c8 d1 e4 f7 g5 h2", "a3 b6 c8 d1 e5 f7 g2 h4",
    "a3 b6 c8 d2 e4 f1 g7 h5", "a3 b7 c2 d8 e5 f1 g4 h6",
    "a3 b7 c2 d8 e6 f4 g1 h5", "a3 b8 c4 d7 e1 f6 g2 h5",
    "a4 b1 c5 d8 e2 f7 g3 h6", "a4 b1 c5 d8 e6 f3 g7 h2",
    "a4 b2 c5 d8 e6 f1 g3 h7", "a4 b2 c7 d3 e6 f8 g1 h5",
    "a4 b2 c7 d3 e6 f8 g5 h1", "a4 b2 c7 d5 e1 f8 g6 h3",
    "a4 b2 c8 d5 e7 f1 g3 h6", "a4 b2 c8 d6 e1 f3 g5 h7",
    "a4 b6 c1 d5 e2 f8 g3 h7", "a4 b6 c8 d2 e7 f1 g3 h5",
    "a4 b6 c8 d3 e1 f7 g5 h2", "a4 b7 c1 d8 e5 f2 g6 h3",
    "a4 b7 c3 d8 e2 f5 g1 h6", "a4 b7 c5 d2 e6 f1 g3 h8",
    "a4 b7 c5 d3 e1 f6 g8 h2", "a4 b8 c1 d3 e6 f2 g7 h5",
    "a4 b8 c1 d5 e7 f2 g6 h3", "a4 b8 c5 d3 e1 f7 g2 h6",
    "a5 b1 c4 d6 e8 f2 g7 h3", "a5 b1 c8 d4 e2 f7 g3 h6",
    "a5 b1 c8 d6 e3 f7 g2 h4", "a5 b2 c4 d6 e8 f3 g1 h7",
    "a5 b2 c4 d7 e3 f8 g6 h1", "a5 b2 c6 d1 e7 f4 g8 h3",
    "a5 b2 c8 d1 e4 f7 g3 h6", "a5 b3 c1 d6 e8 f2 g4 h7",
    "a5 b3 c1 d7 e2 f8 g6 h4", "a5 b3 c8 d4 e7 f1 g6 h2",
    "a5 b7 c1 d3 e8 f6 g4 h2", "a5 b7 c1 d4 e2 f8 g6 h3",
    "a5 b7 c2 d4 e8 f1 g3 h6", "a5 b7 c2 d6 e3 f1 g4 h8",
    "a5 b7 c2 d6 e3 f1 g8 h4", "a5 b7 c4 d1 e3 f8 g6 h2",
    "a5 b8 c4 d1 e3 f6 g2 h7", "a5 b8 c4 d1 e7 f2 g6 h3",
    "a6 b1 c5 d2 e8 f3 g7 h4", "a6 b2 c7 d1 e3 f5 g8 h4",
    "a6 b2 c7 d1 e4 f8 g5 h3", "a6 b3 c1 d7 e5 f8 g2 h4",
    "a6 b3 c1 d8 e4 f2 g7 h5", "a6 b3 c1 d8 e5 f2 g4 h7",
    "a6 b3 c5 d7 e1 f4 g2 h8", "a6 b3 c5 d8 e1 f4 g2 h7",
    "a6 b3 c7 d2 e4 f8 g1 h5", "a6 b3 c7 d2 e8 f5 g1 h4",
    "a6 b3 c7 d4 e1 f8 g2 h5", "a6 b4 c1 d5 e8 f2 g7 h3",
    "a6 b4 c2 d8 e5 f7 g1 h3", "a6 b4 c7 d1 e3 f5 g2 h8",
    "a6 b4 c7 d1 e8 f2 g5 h3", "a6 b8 c2 d4 e1 f7 g5 h3",
    "a7 b1 c3 d8 e6 f4 g2 h5", "a7 b2 c4 d1 e8 f5 g3 h6",
    "a7 b2 c6 d3 e1 f4 g8 h5", "a7 b3 c1 d6 e8 f5 g2 h4",
    "a7 b3 c8 d2 e5 f1 g6 h4", "a7 b4 c2 d5 e8 f1 g3 h6",
    "a7 b4 c2 d8 e6 f1 g3 h5", "a7 b5 c3 d1 e6 f8 g2 h4",
    "a8 b2 c4 d1 e7 f5 g3 h6", "a8 b2 c5 d3 e1 f7 g4 h6",
    "a8 b3 c1 d6 e2 f5 g7 h4", "a8 b4 c1 d3 e6 f2 g7 h5",
  ],
  "Should solve the 8-Queens puzzle.",
);
console.timeEnd("8-Queens");

console.time("10-Queens");
assert_equal(
  solve(n_queens(10)).length,
  724,
  "Should count the solutions to the 10-Queens puzzle.",
);
console.timeEnd("10-Queens");


// SUDOKU

// NB: 1≤x≤9, 1≤y≤9, 1≤c≤9.
function sudoku_cell(x, y, c) {
  return y * 81 + x * 9 + c - 90;
}

const sudoku_constraints = [];

// Each square must contain exactly one color.
for(let y = 1; y < 10; y++) {
  for(let x = 1; x < 10; x++) {
    // At least one color.
    sudoku_constraints.push([
      sudoku_cell(x, y, 1),
      sudoku_cell(x, y, 2),
      sudoku_cell(x, y, 3),
      sudoku_cell(x, y, 4),
      sudoku_cell(x, y, 5),
      sudoku_cell(x, y, 6),
      sudoku_cell(x, y, 7),
      sudoku_cell(x, y, 8),
      sudoku_cell(x, y, 9),
    ]);

    // At most one color.
    for(let j = 2; j < 10; j++) {
      for(let i = 1; i < j; i++) {
        sudoku_constraints.push([-sudoku_cell(x, y, i), -sudoku_cell(x, y, j)]);
      }
    }
  }
}

// Each row must contain each color.
for(let y = 1; y < 10; y++) {
  for(let c = 1; c < 10; c++) {
    sudoku_constraints.push([
      sudoku_cell(1, y, c),
      sudoku_cell(2, y, c),
      sudoku_cell(3, y, c),
      sudoku_cell(4, y, c),
      sudoku_cell(5, y, c),
      sudoku_cell(6, y, c),
      sudoku_cell(7, y, c),
      sudoku_cell(8, y, c),
      sudoku_cell(9, y, c),
    ]);
  }
}

// Each column must contain each color.
for(let x = 1; x < 10; x++) {
  for(let c = 1; c < 10; c++) {
    sudoku_constraints.push([
      sudoku_cell(x, 1, c),
      sudoku_cell(x, 2, c),
      sudoku_cell(x, 3, c),
      sudoku_cell(x, 4, c),
      sudoku_cell(x, 5, c),
      sudoku_cell(x, 6, c),
      sudoku_cell(x, 7, c),
      sudoku_cell(x, 8, c),
      sudoku_cell(x, 9, c),
    ]);
  }
}

// Each 3x3 block must contain each color.
for(let y = 1; y < 10; y += 3) {
  for(let x = 1; x < 10; x += 3) {
    for(let c = 1; c < 10; c++) {
      sudoku_constraints.push([
        sudoku_cell(x + 0, y + 0, c),
        sudoku_cell(x + 1, y + 0, c),
        sudoku_cell(x + 2, y + 0, c),
        sudoku_cell(x + 0, y + 1, c),
        sudoku_cell(x + 1, y + 1, c),
        sudoku_cell(x + 2, y + 1, c),
        sudoku_cell(x + 0, y + 2, c),
        sudoku_cell(x + 1, y + 2, c),
        sudoku_cell(x + 2, y + 2, c),
      ]);
    }
  }
}

function to_sudoku(solution) {
  const chars = [
    " ", " ", " ", "|", " ", " ", " ", "|", " ", " ", " ", "\n",
    " ", " ", " ", "|", " ", " ", " ", "|", " ", " ", " ", "\n",
    " ", " ", " ", "|", " ", " ", " ", "|", " ", " ", " ", "\n",
    "-", "-", "-", "+", "-", "-", "-", "+", "-", "-", "-", "\n",
    " ", " ", " ", "|", " ", " ", " ", "|", " ", " ", " ", "\n",
    " ", " ", " ", "|", " ", " ", " ", "|", " ", " ", " ", "\n",
    " ", " ", " ", "|", " ", " ", " ", "|", " ", " ", " ", "\n",
    "-", "-", "-", "+", "-", "-", "-", "+", "-", "-", "-", "\n",
    " ", " ", " ", "|", " ", " ", " ", "|", " ", " ", " ", "\n",
    " ", " ", " ", "|", " ", " ", " ", "|", " ", " ", " ", "\n",
    " ", " ", " ", "|", " ", " ", " ", "|", " ", " ", " ", "\n",
  ];

  for(let y of solution) {
    if(!(y >= 1)) { continue; }

    y -= 1;

    const c = y % 9;
    y = Math.floor((y - c) / 9);

    const x = y % 9;
    y = Math.floor((y - x) / 9);

    let i = y * 12 + x;
    if(x >= 3) { i +=  1; }
    if(x >= 6) { i +=  1; }
    if(y >= 3) { i += 12; }
    if(y >= 6) { i += 12; }

    chars[i] = c + 1;
  }

  return chars.join("");
}

// FIXME: This doesn't complete because my shitty toy SAT solver is garbage.
// MiniSAT, which is a REAL solver, takes 1.3s to find a solution. If I wrote
// a REAL solver in JS, it'd probably be an order of magnitude slower, and
// that's at best. So my crappy toy solver isn't even in the same league and
// would probably take hours to find a solution.
//
// Welp, I guess that means it's time to write a real solver.
// This puzzle is taken from Gordon Royle's (now defunct) minimum Sudoku
// collection[1]. With 17 clues, it's among the hardest Sudoku puzzles.
//
// [1]: http://school.maths.uwa.edu.au/~gordon/sudokumin.php
console.log(
  to_sudoku(
    solve([
      [sudoku_cell(8, 1, 1)],
      [sudoku_cell(1, 2, 4)],
      [sudoku_cell(2, 3, 2)],
      [sudoku_cell(5, 4, 5)],
      [sudoku_cell(7, 4, 4)],
      [sudoku_cell(9, 4, 7)],
      [sudoku_cell(3, 5, 8)],
      [sudoku_cell(7, 5, 3)],
      [sudoku_cell(3, 6, 1)],
      [sudoku_cell(5, 6, 9)],
      [sudoku_cell(1, 7, 3)],
      [sudoku_cell(4, 7, 4)],
      [sudoku_cell(7, 7, 2)],
      [sudoku_cell(2, 8, 5)],
      [sudoku_cell(4, 8, 1)],
      [sudoku_cell(4, 9, 8)],
      [sudoku_cell(6, 9, 6)],
      ...sudoku_constraints,
    ]),
  ),
);
