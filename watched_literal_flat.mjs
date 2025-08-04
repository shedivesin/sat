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
    if(l < 1) { return []; } // UNSAT

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
  const watch = new Uint32Array(n * 2).fill(m);
  const next = new Uint32Array(m).fill(m);
  const move = new Uint32Array(n);

  for(let i = 0, k = 0; i < m; i++) {
    start[i] = k;

    const clause = formula[i];
    const l = clause.length;
    for(let j = 0; j < l; j++, k++) {
      const literal = clause[j];
      literals[k] = (Math.abs(literal) - 1) * 2 + (literal >>> 31);
    }
  }

  start[m] = p;

  for(let i = m; i--; ) {
    const literal = formula[i][0];
    const j = (Math.abs(literal) - 1) * 2 + (literal >>> 31);
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
  let d = 0;

  // B2. Rejoice or choose.
  // while(d < m) {
    move[d] = (watch[d << 1] >= m) | (watch[(d << 1) | 1] < m);
    let l = (d << 1) | move[d];
    console.log("d=%d move[d]=%d l=%d", d, move[d], l);

    // B3. Remove -l if possible.
    // FIXME
  //}
}

solve([ 
  [ 1,  2, -3],
  [ 2,  3, -4], 
  [ 3,  4,  1],
  [ 4, -1,  2],
  [-1, -2,  3],  
  [-2, -3,  4],
  [-3, -4, -1],
]);
