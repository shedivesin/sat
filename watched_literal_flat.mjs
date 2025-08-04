function solve(formula) {
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
      if(!(variable < 2147483649)) { throw new RangeError("Too many variables"); }

      if(variable > n) { n = variable; }
    }
  }

  console.log("m=%d n=%d p=%d", m, n, p);

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

  console.log(
    "literals=(%s)\nstart=(%s)\nwatch=(%s)\nnext=(%s)",
    literals.join(" "),
    start.join(" "),
    watch.join(" "),
    next.join(" "),
  );

  // BACKTRACKING SEARCH
  // B1. Initialize.
  // B2. Rejoice or choose.
  b2: for(let d = 0; d < n; ) {
    move[d] = (watch[d << 1] >= m) | (watch[(d << 1) | 1] < m);
    let l = (d << 1) | move[d];

    {
      const w = [];
      for(let j = watch[l ^ 1]; j < m; j = next[j]) {
        w.push(j);
      }

      console.log(
        "\nd=%d move=(%s) l=%d watch[-l]=(%s)",
        d,
        Array.from(move).slice(0, d + 1).join(" "),
        l,
        w.join(" "),
      );
    }

    // B3. Remove -l if possible.
    b3: for(let j = watch[l ^ 1]; j < m; ) {
      const i = start[j];
      const i_p = start[j + 1];
      const j_p = next[j];

      for(let k = i + 1; k < i_p; k++) {
        const l_p = literals[k];
        // If l_p isn't false (e.g. is TBD or is true), then watch it, instead.
        // FIXME: see (57)
        if((l_p >> 1) > d || ((l_p + move[l_p >> 1]) & 1) === 0) {
          console.log("  j=%d swap %d and %d", j, l ^ 1, l_p);
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
      console.log("  j=%d can't stop watching -l", j);

      // B5. Try again.
      b5: for(;;) {
        if(move[d] < 2) {
          move[d] ^= 3;
          l ^= 1;
          j = watch[l ^ 1]; // Necessary since we can't GOTO B3 in JavaScript.
          continue b3;
        }

        // B6. Backtrack.
        if(d < 1) { return null; } // UNSAT
        d--;
      }
    }

    // B4. Advance.
    watch[l ^ 1] = m;
    console.log(
      "literals=(%s)\nwatch=(%s)\nnext=(%s)",
      literals.join(" "),
      watch.join(" "),
      next.join(" "),
    );

    d++;
  }

  // CONVERT OUTPUT AND RETURN
  const solution = new Array(n);
  for(let i = 0; i < n; i++) {
    solution[i] = (i + 1) * (1 - ((move[i] & 1) << 1));
  }

  return solution;
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
