/* ---- Robust hybrid solver: parser, truth-table, and natural deduction ---- */

const premisesInput = document.getElementById('premises');
const conclusionInput = document.getElementById('conclusion');
const solveBtn = document.getElementById('solve-btn');
const clearBtn = document.getElementById('clear-btn');
const exampleBtn = document.getElementById('example-btn');
const resultContainer = document.getElementById('result-container');
const stepsContainer = document.getElementById('steps');
const finalResultContainer = document.getElementById('final-result');

const example = {
    premises: `(P | Q) -> R\nP\n~R`,
    conclusion: `~Q`
};

exampleBtn.addEventListener('click', () => {
    premisesInput.value = example.premises;
    conclusionInput.value = example.conclusion;
});

clearBtn.addEventListener('click', () => {
    premisesInput.value = '';
    conclusionInput.value = '';
    resultContainer.classList.add('hidden');
    stepsContainer.innerHTML = '';
    finalResultContainer.innerHTML = '';
});

solveBtn.addEventListener('click', solve);

/* ---------------- Tokenizer + Precedence parser ---------------- */
function tokenize(s) {
    s = s.replace(/->/g, ' -> ');
    s = s.replace(/\(/g, ' ( ').replace(/\)/g, ' ) ');
    s = s.replace(/~/g, ' ~ ');
    s = s.replace(/&/g, ' & ').replace(/\|/g, ' | ');
    return s.trim().split(/\s+/).filter(Boolean);
}

function parseFromString(str) {
    const tokens = tokenize(str);
    let i = 0;

    function peek() { return tokens[i]; }
    function consume(tok) { if (peek() === tok) { i++; return true; } return false; }

    // Grammar (with precedence)
    // implication := orExpr ( '->' implication )?
    // orExpr := andExpr ( '|' andExpr )*
    // andExpr := notExpr ( '&' notExpr )*
    // notExpr := '~' notExpr | primary
    // primary := VAR | '(' implication ')'

    function parseImplication() {
        let left = parseOr();
        if (peek() === '->') {
            consume('->');
            const right = parseImplication(); // right-associative
            return { type: 'imp', left, right };
        }
        return left;
    }

    function parseOr() {
        let node = parseAnd();
        while (peek() === '|') {
            consume('|');
            const right = parseAnd();
            node = { type: 'or', left: node, right };
        }
        return node;
    }

    function parseAnd() {
        let node = parseNot();
        while (peek() === '&') {
            consume('&');
            const right = parseNot();
            node = { type: 'and', left: node, right };
        }
        return node;
    }

    function parseNot() {
        if (peek() === '~') {
            consume('~');
            const expr = parseNot();
            return { type: 'not', expr };
        }
        return parsePrimary();
    }

    function parsePrimary() {
        if (peek() === '(') {
            consume('(');
            const expr = parseImplication();
            if (!consume(')')) throw new Error('Missing closing )');
            return expr;
        }
        const t = peek();
        if (!t) throw new Error('Unexpected end of input');
        i++;
        // variable token
        return { type: 'var', name: t };
    }

    const root = parseImplication();
    if (i < tokens.length) throw new Error('Unexpected token: ' + tokens[i]);
    return root;
}

/* ---------------- Expression to canonical string ---------------- */
function exprToStr(e) {
    if (!e) return '';
    switch (e.type) {
        case 'var': return e.name;
        case 'not': {
            const inner = e.expr;
            // show ~X or ~(complex)
            return inner.type === 'var' ? `~${exprToStr(inner)}` : `~(${exprToStr(inner)})`;
        }
        case 'and':
            return `(${exprToStr(e.left)} & ${exprToStr(e.right)})`;
        case 'or':
            return `(${exprToStr(e.left)} | ${exprToStr(e.right)})`;
        case 'imp':
            return `(${exprToStr(e.left)} -> ${exprToStr(e.right)})`;
        default: return JSON.stringify(e);
    }
}

/* ---------------- Evaluator ---------------- */
function evalExpr(e, assignment) {
    switch (e.type) {
        case 'var': return Boolean(assignment[e.name]);
        case 'not': return !evalExpr(e.expr, assignment);
        case 'and': return evalExpr(e.left, assignment) && evalExpr(e.right, assignment);
        case 'or': return evalExpr(e.left, assignment) || evalExpr(e.right, assignment);
        case 'imp': return (!evalExpr(e.left, assignment)) || evalExpr(e.right, assignment);
    }
}

/* ---------------- Forward-chaining natural deduction engine ----------------
   - Returns an object { map, order } where:
     map: Map(exprStr -> { expr, reason, derivedFrom: [strings], stepOrder })
     order: array of exprStr in the order they were added (useful for nice printing)
*/
function forwardChain(premiseExprs, goalExpr, extraAssumptions = []) {
    const goalStr = exprToStr(goalExpr);
    const map = new Map();
    const order = [];

    function addExpr(expr, reason, derivedFrom = []) {
        const s = exprToStr(expr);
        if (map.has(s)) return false;
        const entry = { expr, reason, derivedFrom, stepOrder: order.length + 1 };
        map.set(s, entry);
        order.push(s);
        // 🚀 stop early if goal reached
        if (s === goalStr) throw { found: true };
        return true;
    }

    // initialize
    premiseExprs.forEach((ex, idx) => addExpr(ex, `Premise ${idx + 1}`));
    extraAssumptions.forEach((ex) => addExpr(ex, `Assumption`));

    let safety = 0;
    try {
        let changed = true;
        while (changed && safety < 5000) {
            changed = false;
            safety++;

            const keys = Array.from(order);

            for (const s of keys) {
                const e = map.get(s).expr;

                // Simplification
                if (e.type === 'and') {
                    if (addExpr(e.left, `Simplification from ${s}`, [s])) changed = true;
                    if (addExpr(e.right, `Simplification from ${s}`, [s])) changed = true;
                }

                for (const t of keys) {
                    if (s === t) continue;
                    const f = map.get(t).expr;

                    // Modus Ponens
                    if (e.type === 'imp') {
                        const leftStr = exprToStr(e.left);
                        if (map.has(leftStr)) {
                            if (addExpr(e.right, `Modus Ponens from ${s} and ${leftStr}`, [s, leftStr])) changed = true;
                        }
                        // Modus Tollens
                        const negRightStr = exprToStr({ type: 'not', expr: e.right });
                        if (map.has(negRightStr)) {
                            const negLeft = { type: 'not', expr: e.left };
                            if (addExpr(negLeft, `Modus Tollens from ${s} and ${negRightStr}`, [s, negRightStr])) changed = true;
                        }
                        // Hypothetical Syllogism
                        if (f.type === 'imp' && JSON.stringify(e.right) === JSON.stringify(f.left)) {
                            const newImp = { type: 'imp', left: e.left, right: f.right };
                            if (addExpr(newImp, `Hypothetical Syllogism from ${s} and ${t}`, [s, t])) changed = true;
                        }
                    }

                    // Disjunctive Syllogism
                    if (e.type === 'or') {
                        const notA = exprToStr({ type: 'not', expr: e.left });
                        const notB = exprToStr({ type: 'not', expr: e.right });
                        if (map.has(notA)) {
                            if (addExpr(e.right, `Disjunctive Syllogism from ${s} and ${notA}`, [s, notA])) changed = true;
                        }
                        if (map.has(notB)) {
                            if (addExpr(e.left, `Disjunctive Syllogism from ${s} and ${notB}`, [s, notB])) changed = true;
                        }
                    }

                    // ✅ Conjunction Introduction only if GOAL is a conjunction
                    if (goalExpr.type === 'and') {
                        const aStr = exprToStr(e), bStr = exprToStr(f);
                        if (aStr !== bStr && map.has(aStr) && map.has(bStr)) {
                            if ((aStr === exprToStr(goalExpr.left) && bStr === exprToStr(goalExpr.right)) ||
                                (bStr === exprToStr(goalExpr.left) && aStr === exprToStr(goalExpr.right))) {
                                const conj = { type: 'and', left: e, right: f };
                                if (addExpr(conj, `Conjunction Introduction from ${aStr} and ${bStr}`, [aStr, bStr])) changed = true;
                            }
                        }
                    }
                }
            }
        }
    } catch (e) {
        if (e.found) {
            return { map, order, goalFound: true };
        } else {
            throw e;
        }
    }

    return { map, order, goalFound: map.has(goalStr) };
}

/* ---------------- Attempt natural deduction with implication-intro support ----------------
   - premises: array of parsed expressions
   - goalExpr: parsed expression
   returns: { derived: boolean, stepsHtml: string } where stepsHtml is formatted human steps
*/
function attemptDeductionWithProof(premises, goalExpr) {
    const run = forwardChain(premises, goalExpr);
    if (run.goalFound) {
        return { derived: true, html: buildStepsHtmlFromMap(run, 'Proof (direct derivation)') };
    }

    if (goalExpr.type === 'imp') {
        const A = goalExpr.left;
        const B = goalExpr.right;
        const run2 = forwardChain(premises, B, [A]);
        if (run2.goalFound) {
            return { derived: true, html: buildStepsHtmlFromMap(run2, 'Proof (→-intro)', true, exprToStr(A), exprToStr(B)) };
        }
    }
    return { derived: false, html: null };
}

/* Build pretty steps HTML from a forwardChain run */
function buildStepsHtmlFromMap(run, title, isAssumptionRun = false, assumptionStr = '', derivedStr = '') {
    const { map, order } = run;
    let lines = [];
    let idx = 1;
    for (const s of order) {
        const e = map.get(s);
        lines.push(`${idx}. ${s}    — ${e.reason}`);
        idx++;
    }
    if (isAssumptionRun) {
        lines.push(`${idx}. ${assumptionStr} -> ${derivedStr}    — →-Introduction (discharge assumption)`);
    }
    return `<h3 class="font-semibold mb-2">${title}</h3><pre class="bg-gray-50 p-2 rounded text-sm">${lines.join('\n')}</pre>`;
}

/* ---------------- Truth table solver + UI render ---------------- */
function solve() {
    stepsContainer.innerHTML = '';
    finalResultContainer.innerHTML = '';

    const premisesRaw = premisesInput.value.split('\n').map(s => s.trim()).filter(s => s.length > 0);
    const conclusionRaw = conclusionInput.value.trim();

    if (!premisesRaw.length || !conclusionRaw) {
        alert('Please provide premises and a conclusion.');
        return;
    }

    // parse formulas (catch parse errors)
    let premiseExprs = [];
    try {
        premiseExprs = premisesRaw.map(parseFromString);
    } catch (err) {
        alert('Error parsing premises: ' + err.message);
        return;
    }
    let conclusionExpr;
    try {
        conclusionExpr = parseFromString(conclusionRaw);
    } catch (err) {
        alert('Error parsing conclusion: ' + err.message);
        return;
    }

    // collect variables
    const vars = new Set();
    function collectVars(e) {
        if (!e) return;
        if (e.type === 'var') vars.add(e.name);
        else if (e.type === 'not') collectVars(e.expr);
        else { collectVars(e.left); collectVars(e.right); }
    }
    premiseExprs.forEach(collectVars);
    collectVars(conclusionExpr);
    const varList = [...vars];

    // truth table
    let valid = true;
    let consistent = false;
    const truthTable = [];

    const total = 1 << varList.length;
    for (let mask = 0; mask < total; mask++) {
        const assignment = {};
        varList.forEach((v, i) => assignment[v] = Boolean(mask & (1 << i)));
        const premisesTrue = premiseExprs.every(p => evalExpr(p, assignment));
        const conclusionTrue = evalExpr(conclusionExpr, assignment);
        if (premisesTrue) {
            consistent = true;
            if (!conclusionTrue) valid = false;
        }
        truthTable.push({ assignment, premisesTrue, conclusionTrue });
    }

    // render truth table
    resultContainer.classList.remove('hidden');
    stepsContainer.innerHTML = '';

    // header
    const table = document.createElement('table');
    table.className = 'min-w-full border border-gray-300 text-sm text-center';
    let header = '<tr>';
    varList.forEach(v => header += `<th class="border px-2 py-1">${v}</th>`);
    premisesRaw.forEach(p => header += `<th class="border px-2 py-1">${p}</th>`);
    header += `<th class="border px-2 py-1">${conclusionRaw}</th></tr>`;
    table.innerHTML = header;

    // rows
    truthTable.forEach(row => {
        let tr = '<tr>';
        varList.forEach(v => tr += `<td class="border px-2 py-1">${row.assignment[v] ? 'T' : 'F'}</td>`);
        premisesRaw.forEach((p, i) => tr += `<td class="border px-2 py-1">${row.premisesTrue ? 'T' : 'F'}</td>`);
        tr += `<td class="border px-2 py-1">${row.conclusionTrue ? 'T' : 'F'}</td>`;
        tr += '</tr>';
        table.innerHTML += tr;
    });

    stepsContainer.appendChild(table);

    // final truth-table based verdict
    if (!consistent) {
        finalResultContainer.className = 'mt-4 text-lg font-bold p-4 rounded-lg bg-yellow-100 text-yellow-800';
        finalResultContainer.textContent = 'Premises are inconsistent (unsatisfiable). Any conclusion follows.';
    } else if (valid) {
        finalResultContainer.className = 'mt-4 text-lg font-bold p-4 rounded-lg bg-green-100 text-green-800';
        finalResultContainer.textContent = `Conclusion "${conclusionRaw}" is VALID (truth-table confirmed).`;
    } else {
        finalResultContainer.className = 'mt-4 text-lg font-bold p-4 rounded-lg bg-red-100 text-red-800';
        finalResultContainer.textContent = `Conclusion "${conclusionRaw}" is INVALID (truth-table confirmed).`;
    }

    // Try natural deduction
    const proofAttempt = attemptDeductionWithProof(premiseExprs, conclusionExpr);
    if (proofAttempt.derived) {
        // prepend a separator and the proof steps
        stepsContainer.innerHTML += proofAttempt.html;
    } else {
        // Show a helpful message: if truth-table says valid but no derivation, say that
        let msg;
        if (valid) {
            msg = `<p class="mt-4 text-gray-700">No direct natural-deduction derivation found with the current simple rules, but truth-table confirms validity.</p>`;
        } else {
            msg = `<p class="mt-4 text-gray-700">No natural-deduction derivation found. Truth-table shows the argument is invalid.</p>`;
        }
        stepsContainer.innerHTML += msg;
    }
}