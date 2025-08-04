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
  // FIXME: Allocate one big ArrayBuffer and slice these out of it!
  const literals = new Uint32Array(p);
  const start = new Uint32Array(m + 1);
  const watch = new Uint32Array(n << 1).fill(m);
  const next = new Uint32Array(m).fill(m);
  const move = new Uint32Array(n);

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
  // B1. Initialize.
  // B2. Rejoice or choose.
  b2: for(let d = 0; d < n; ) {
    move[d] = (watch[d << 1] >= m) | (watch[(d << 1) | 1] < m);
    let l = (d << 1) | move[d];

    // B3. Remove -l if possible.
    b3: for(let j = watch[l ^ 1]; j < m; ) {
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
          continue b3;
        }
      }

      // Can't stop watching -l.
      watch[l ^ 1] = j;

      // B5. Try again.
      b5: for(;;) {
        if(move[d] < 2) {
          move[d] ^= 3;
          l ^= 1;
          j = watch[l ^ 1];
          continue b3;
        }

        // B6. Backtrack.
        if(d < 1) { return null; } // UNSAT

        d--;
        l = (d << 1) | move[d];
      }
    }

    // B4. Advance.
    watch[l ^ 1] = m;
    d++;
  }

  // CONVERT OUTPUT AND RETURN
  return mapper(move);
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
  ]),
);
console.log("(should be", [-1, 2, undefined, 4], ")");

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

console.time("4 queens");
console.log(solve(n_queens(4), to_chess_notation));
console.timeEnd("4 queens");
console.time("8 queens");
console.log(solve(n_queens(8), to_chess_notation));
console.timeEnd("8 queens");
console.time("10 queens");
console.log(solve(n_queens(10), to_chess_notation));
console.timeEnd("10 queens");
console.time("20 queens");
console.log(solve(n_queens(20), to_chess_notation));
console.timeEnd("20 queens");
