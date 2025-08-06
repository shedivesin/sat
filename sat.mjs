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
// There are a number of ways to solve the problem, each with their own
// peculiarities. The best overall introduction, of course, is Donald Knuth,
// The Art of Computer Programming, vol. 4 fasc. 6 "Satisfiability." I've
// implemented (versions of) his Algorithm A, B, P, and W; the version seen
// here is a version of Algorithm B, as being pretty simple and fast enough
// for the toy problems I'm playing with. (Honestly, if you want performance,
// JavaScript isn't the way to implement your solution.)

function to_dimacs(move) {
  const n = move.length;
  const solution = new Array(n);
  for(let i = 0; i < n; i++) {
    solution[i] = (i + 1) * (1 - ((move[i] & 1) << 1));
  }

  return solution;
}

function solve(formula, mapper=to_dimacs) {
  // VALIDATE INPUT AND DETERMINE CNF PARAMETERS
  if(!Array.isArray(formula)) { throw new TypeError("Invalid formula"); }

  const m = formula.length;
  let n = 0;
  let p = 0;
  for(let i = 0; i < m; i++) {
    const clause = formula[i];
    if(!Array.isArray(clause)) { throw new TypeError("Invalid clause"); }

    const l = clause.length;
    if(l < 1) { return null; } // UNSAT

    p += l;

    for(let j = 0; j < l; j++) {
      const literal = clause[j];
      if(!Number.isInteger(literal)) { throw new TypeError("Invalid literal"); }
 
      const variable = Math.abs(literal);
      if(!(variable >= 1)) { throw new RangeError("Invalid variable"); }

      if(variable > n) { n = variable; }
    }
  }

  // ALLOCATE AND INITIALIZE DATA STRUCTURES
  const buffer = new ArrayBuffer(p * 4 + m * 8 + n * 12 + 4);
  const literals = new Uint32Array(buffer, 0, p);
  const start = new Uint32Array(buffer, p * 4, m + 1);
  const watch = new Uint32Array(buffer, p * 4 + m * 4 + 4, n * 2).fill(m);
  const next = new Uint32Array(buffer, p * 4 + m * 4 + n * 8 + 4, m).fill(m);
  const move = new Uint32Array(buffer, p * 4 + m * 8 + n * 8 + 4, n);

  for(let i = 0, k = 0; i < m; i++) {
    start[i] = k;

    const clause = formula[i];
    const l = clause.length;
    for(let j = 0; j < l; j++, k++) {
      const literal = clause[j];
      literals[k] = ((Math.abs(literal) - 1) << 1) | (literal >>> 31);
    }
  }

  start[m] = p;

  for(let i = m; i--; ) {
    const literal = formula[i][0];
    const j = ((Math.abs(literal) - 1) << 1) | (literal >>> 31);
    next[i] = watch[j];
    watch[j] = i;
  }

  // BACKTRACKING SEARCH
  // B1. Initialize. B2. Rejoice or choose.
  for(let d = 0; d < n; d++) {
    move[d] = (watch[d << 1] >= m) | (watch[(d << 1) | 1] < m);
    let l = (d << 1) | move[d];

    // B3. Remove -l if possible.
    let j = watch[l ^ 1];

    b3: while(j < m) {
      const i = start[j];
      const i_p = start[j + 1];
      const j_p = next[j];

      for(let k = i + 1; k < i_p; k++) {
        const l_p = literals[k];
        // If l_p isn't false (e.g. is TBD or is true), then watch it, instead.
        if((l_p >> 1) > d || ((l_p + move[l_p >> 1]) & 1) === 0) {
          literals[i] = l_p;
          literals[k] = l ^ 1;
          next[j] = watch[l_p];
          watch[l_p] = j;
          j = j_p;
          // FIXME: Is it possible to remove the need for this label?
          continue b3;
        }
      }

      // Can't stop watching -l.
      watch[l ^ 1] = j;

      // B6. Backtrack.
      while(move[d] >= 2) {
        if(d < 1) { return null; } // UNSAT
        d--;
      }

      // B5. Try again.
      move[d] ^= 3;
      // NB: This next line is subtle. Remember that we can enter here from
      // B6, which may have changed d out from under us!
      l = (d << 1) | (move[d] & 1);
      j = watch[l ^ 1];
    }

    // B4. Advance.
    watch[l ^ 1] = m;
  }

  // CONVERT OUTPUT AND RETURN
  return mapper(move);
}

assert_equal(
  solve([]),
  [],
  "Should solve an empty formula.",
);

assert_equal(
  solve([[]]),
  null,
  "Should fail to solve a formula with an empty clause.",
);

assert_equal(
  solve([[1, 2], [-1, 3], [-3, 4], [1]]),
  [1, 2, 3, 4],
  "Should solve a simple 2SAT formula.",
);

assert_equal(
  solve([
    [1, 2, -3], [2, 3, -4], [1, 3, 4], [-1, 2, 4],
    [-1, -2, 3], [-2, -3, 4], [-3, -4, -1], [1, -2, -4],
  ]),
  null,
  "Should fail to solve the \"shortest interesting formula in 3CNF.\"",
);

assert_equal(
  solve([
    [1, 2, -3], [2, 3, -4], [1, 3, 4], [-1, 2, 4],
    [-1, -2, 3], [-2, -3, 4], [-3, -4, -1],
  ]),
  [-1, 2, -3, 4], // NB: 3 can be positive or negative.
  "Should solve Knuth's eq. 7, \"nice test data.\""
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
  [-1, -2, 3, 4, -5, -6, 7, 8],
  "Should solve Knuth's sample van der Waerden problem.",
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
        const x1 = x + y1 - y2;
        if(x1 >= 0) { formula.push([-(y1 * n + x + 1), -(y2 * n + x1 + 1)]); }

        formula.push([-(y1 * n + x + 1), -(y2 * n + x + 1)]);

        const x2 = x + y2 - y1;
        if(x2 <  n) { formula.push([-(y1 * n + x + 1), -(y2 * n + x2 + 1)]); }
      }
    }
  }

  return formula;
}

function to_chess_notation(move) {
  const n = move.length;
  const k = Math.floor(Math.sqrt(n));
  if(!(k >= 1 && k < 27 && n === k * k)) { throw new Error("Invalid board size"); }

  const squares = [];
  for(let i = 0; i < n; i++) {
    if(move[i] & 1) { continue; }

    const x = i % k;
    const y = Math.floor(i / k);
    if(!(x >= 0 && x < k && y >= 0 && y < k)) { continue; }

    squares.push(String.fromCharCode(97 + x) + (y + 1));
  }

  return squares.sort().join(" ");
}

assert_equal(
  solve(n_queens(3), to_chess_notation),
  null,
  "Should fail to solve the 3-Queens puzzle.",
);

console.time("4-Queens");
assert_equal(
  solve(n_queens(4), to_chess_notation),
  "a2 b4 c1 d3", // NB: One of 2 solutions.
  "Should solve the 4-Queens puzzle.",
);
console.timeEnd("4-Queens");

console.time("8-Queens");
assert_equal(
  solve(n_queens(8), to_chess_notation),
  "a3 b6 c4 d2 e8 f5 g7 h1", // NB: One of 92 solutions.
  "Should solve the 8-Queens puzzle.",
);
console.timeEnd("8-Queens");

console.time("12-Queens");
assert_equal(
  solve(n_queens(12), to_chess_notation),
  "a6 b8 c5 d11 e4 f10 g7 h3 i12 j2 k9 l1", // NB: One of 14,200 solutions.
  "Should solve the 12-Queens puzzle.",
);
console.timeEnd("12-Queens");


// SUDOKU

// NB: 1≤x≤9, 1≤y≤9, 1≤c≤9.
function sudoku_cell(x, y, c) {
  return y * 81 + x * 9 + c - 90;
}

function sudoku(puzzle) {
  const formula = [];

  // Each given cell is required.
  for(let y = 1, i = 0; y < 10; y++) {
    for(let x = 1; x < 10; x++, i++) {
      const c = puzzle[i];
      if(c >= 1) { formula.push([sudoku_cell(x, y, c)]); }
    }
  }

  // Each square must contain exactly one color.
  for(let y = 1; y < 10; y++) {
    for(let x = 1; x < 10; x++) {
      // At least one color.
      formula.push([
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
          formula.push([-sudoku_cell(x, y, i), -sudoku_cell(x, y, j)]);
        }
      }
    }
  }

  // Each row must contain each color.
  for(let y = 1; y < 10; y++) {
    for(let c = 1; c < 10; c++) {
      formula.push([
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
      formula.push([
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
        formula.push([
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

  return formula;
}

function to_sudoku_cells(move) {
  const n = move.length;
  const solution = new Array(81);

  for(let i = 0, j = 0; i < n; i++) {
    if(move[i] & 1) { continue; }
    solution[j++] = (i % 9) + 1;
  }

  return solution;
}

console.time("Sudoku");
assert_equal(
  solve(
    sudoku([
      0, 0, 0,  0, 0, 0,  0, 1, 0,
      4, 0, 0,  0, 0, 0,  0, 0, 0,
      0, 2, 0,  0, 0, 0,  0, 0, 0,

      0, 0, 0,  0, 5, 0,  4, 0, 7,
      0, 0, 8,  0, 0, 0,  3, 0, 0,
      0, 0, 1,  0, 9, 0,  0, 0, 0,

      3, 0, 0,  4, 0, 0,  2, 0, 0,
      0, 5, 0,  1, 0, 0,  0, 0, 0,
      0, 0, 0,  8, 0, 6,  0, 0, 0,
    ]),
    to_sudoku_cells,
  ),
  [
    6, 9, 3,  7, 8, 4,  5, 1, 2,
    4, 8, 7,  5, 1, 2,  9, 3, 6,
    1, 2, 5,  9, 6, 3,  8, 7, 4,

    9, 3, 2,  6, 5, 1,  4, 8, 7,
    5, 6, 8,  2, 4, 7,  3, 9, 1,
    7, 4, 1,  3, 9, 8,  6, 2, 5,

    3, 1, 9,  4, 7, 5,  2, 6, 8,
    8, 5, 6,  1, 2, 9,  7, 4, 3,
    2, 7, 4,  8, 3, 6,  1, 5, 9,
  ],
  "Should solve a hard Sudoku puzzle.",
);
console.timeEnd("Sudoku");
