import tatsu

GRAMMAR = '''
    @@grammar::Problog


    start = program $ ;

    program
        =
        { rule | query }*
        ;

    rule
        =
        [ probability '::' ] normal_rule '.'
        ;

    normal_rule
        =
        atom [ ':-' body ]
        ;

    body 
        =
        atom { ',' atom }
        ;

    atom 
        = 
        /[a-z]([a-zA-Z0-9_])*/ [ '(' input ')' ]
        ;

    input 
        =
        term { ',' term }
        ;

    term 
        =
        /[a-zA-Z0-9'"]*/
        ;

    probability
        =
        | '0.' /[0-9]*/
        | '1'
        | '0'
        ;

    query
        =
        'query(' atom ').'
        ;
'''


with open('parser.py', mode='wb') as file_out:
    file_out.write(tatsu.to_python_sourcecode(GRAMMAR).encode())

