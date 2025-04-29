import re
import numpy as np
from sympy import symbols, sympify, to_dnf, simplify_logic, expand, Xor
from sympy.parsing.sympy_parser import parse_expr
from sympy.printing.latex import latex
from sympy.logic.boolalg import to_anf, And, Or, Not, Implies, Equivalent
from flask import Flask, request, render_template, jsonify

app = Flask(__name__)


def parse_latex_boolean(latex_expr):
    replacements = [
        (r'\\overline\{([^}]+)\}', r'~\1'),
        (r'\\lnot\s*([a-zA-Z0-9_]+)', r'~\1'),
        (r'\\neg\s*([a-zA-Z0-9_]+)', r'~\1'),
        (r'([a-zA-Z0-9_]+)\'', r'~\1'),
        (r'\\land', '&'),
        (r'\\wedge', '&'),
        (r'\\cdot', '&'),
        (r'\*', '&'),
        (r'\\lor', '|'),
        (r'\\vee', '|'),
        (r'\+', '|'),
        (r'\\oplus', '^'),
        (r'\\bigoplus', '^'),
        (r'\\Rightarrow', '>>'),
        (r'\\rightarrow', '>>'),
        (r'\\Leftrightarrow', '<<>>'),
        (r'\\leftrightarrow', '<<>>'),
        (r'\\nand', 'nand'),
        (r'\\nor', 'nor'),
        (r'\\xnor', 'xnor'),
        (r'x_([0-9]+)', r'x\1'),
    ]

    processed_expr = latex_expr
    for pattern, replacement in replacements:
        processed_expr = re.sub(pattern, replacement, processed_expr)

    processed_expr = processed_expr.replace(' ', '').replace('\\', '')

    processed_expr = processed_expr.replace('nand', '~(&)')
    processed_expr = processed_expr.replace('nor', '~(|)')
    processed_expr = processed_expr.replace('xnor', '~(^)')
    processed_expr = processed_expr.replace('>>', '>>')
    processed_expr = processed_expr.replace('<<>>', '<<>>')

    return processed_expr


def detect_variables(expr_str):
    return sorted(set(re.findall(r'x\d+', expr_str)),
                  key=lambda x: int(x[1:]))


def convert_to_mdnf(expr_str, variables):
    var_symbols = {var: symbols(var) for var in variables}

    expr_str = expr_str.replace('>>', '>>')
    expr_str = expr_str.replace('<<>>', '<<>>')

    try:
        expr = parse_expr(expr_str, local_dict=var_symbols)

        expr = expr.replace(lambda e: isinstance(e, Implies),
                            lambda e: Or(Not(e.args[0]), e.args[1]))
        expr = expr.replace(lambda e: isinstance(e, Equivalent),
                            lambda e: And(Or(Not(e.args[0]), e.args[1]),
                                          Or(Not(e.args[1]), e.args[0])))

        dnf_expr = to_dnf(expr, simplify=True)
        simplified = simplify_logic(dnf_expr)

        return simplified
    except Exception as e:
        return f"Error in MDNF conversion: {str(e)}"


def convert_to_mcnf(expr_str, variables):
    var_symbols = {var: symbols(var) for var in variables}

    try:
        expr = parse_expr(expr_str, local_dict=var_symbols)

        from sympy.logic.boolalg import to_cnf
        cnf_expr = to_cnf(expr, simplify=True)
        simplified = simplify_logic(cnf_expr)

        return simplified
    except Exception as e:
        return f"Error in MCNF conversion: {str(e)}"


def convert_to_zhegalkin(expr_str, variables):
    var_symbols = {var: symbols(var) for var in variables}

    try:
        expr = parse_expr(expr_str, local_dict=var_symbols)

        anf_expr = to_anf(expr)

        return anf_expr
    except Exception as e:
        return f"Error in Zhegalkin polynomial conversion: {str(e)}"


def sympy_to_latex(sympy_expr):
    latex_str = latex(sympy_expr)

    replacements = [
        (r'\\neg ', r'\\overline{'),
        (r'\\neg ([a-zA-Z][0-9]*)', r'\\overline{\1}'),
        (r'\\vee', r'\\lor'),
        (r'\\wedge', r'\\land'),
        (r'\\oplus', r'\\oplus'),
        (r'\\Rightarrow', r'\\Rightarrow'),
        (r'\\Leftrightarrow', r'\\Leftrightarrow'),
    ]

    result = latex_str
    for pattern, replacement in replacements:
        if '\\overline{' in replacement:
            def replace_neg(match):
                var = match.group(1)
                return f'\\overline{{{var}}}'

            result = re.sub(pattern, replace_neg, result)
        else:
            result = re.sub(pattern, replacement, result)

    open_brackets = result.count('\\overline{')
    close_brackets = result.count('}')
    if open_brackets > close_brackets:
        result += '}' * (open_brackets - close_brackets)

    return result


def truth_table_to_latex(truth_table, variables):
    num_vars = len(variables)
    num_rows = 2 ** num_vars

    latex_table = "\\begin{array}{|" + "c|" * num_vars + "c|}\n\\hline\n"

    header = " & ".join([f"x_{var[1:]}" for var in variables]) + " & f \\\\\n\\hline\n"
    latex_table += header

    for i in range(num_rows):
        binary = format(i, f'0{num_vars}b')
        row_values = [binary[j] for j in range(num_vars)]

        row_values.append(str(int(truth_table[i])))

        latex_table += " & ".join(row_values) + " \\\\\n"

    latex_table += "\\hline\n\\end{array}"

    return latex_table


def generate_truth_table(expr_str, variables):
    var_symbols = [symbols(var) for var in variables]

    try:
        expr = parse_expr(expr_str, local_dict={var: symbols(var) for var in variables})

        num_vars = len(variables)
        num_rows = 2 ** num_vars
        truth_table = []

        for i in range(num_rows):
            binary = format(i, f'0{num_vars}b')

            var_values = {var_symbols[j]: bool(int(binary[j])) for j in range(num_vars)}
            result = expr.subs(var_values)

            if result == True:
                truth_table.append(True)
            else:
                truth_table.append(False)

        return truth_table
    except Exception as e:
        return f"Error generating truth table: {str(e)}"


def process_boolean_expression(latex_expr):
    expr_str = parse_latex_boolean(latex_expr)

    variables = detect_variables(expr_str)

    truth_table = generate_truth_table(expr_str, variables)

    mdnf_expr = convert_to_mdnf(expr_str, variables)
    mcnf_expr = convert_to_mcnf(expr_str, variables)
    zhegalkin_expr = convert_to_zhegalkin(expr_str, variables)

    mdnf_latex = sympy_to_latex(mdnf_expr)
    mcnf_latex = sympy_to_latex(mcnf_expr)
    zhegalkin_latex = sympy_to_latex(zhegalkin_expr)
    tt_latex = truth_table_to_latex(truth_table, variables) if isinstance(truth_table,
                                                                          list) else "Error generating truth table"

    return {
        "original": latex_expr,
        "variables": [f"x_{var[1:]}" for var in variables],
        "mdnf": mdnf_latex,
        "mcnf": mcnf_latex,
        "zhegalkin": zhegalkin_latex,
        "truth_table": tt_latex
    }


@app.route('/')
def home():
    return render_template('index.html')


@app.route('/process', methods=['POST'])
def process():
    data = request.get_json()
    latex_expr = data.get('expression', '')

    if not latex_expr:
        return jsonify({'error': 'Expression is required'})

    try:
        results = process_boolean_expression(latex_expr)
        return jsonify(results)
    except Exception as e:
        return jsonify({'error': str(e)})


@app.route('/templates/index.html')
def serve_template():
    return render_template('index.html')


if __name__ == '__main__':
    app.run(debug=True)