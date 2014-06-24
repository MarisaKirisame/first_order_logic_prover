TEMPLATE = app
CONFIG += console
CONFIG -= app_bundle
CONFIG -= qt
CONFIG += C++11
SOURCES += main.cpp

HEADERS += \
    value_less.hpp \
    example.hpp \
    first_order_logic/deduction_tree.hpp \
    first_order_logic/first_order_logic.hpp \
    first_order_logic/function.hpp \
    first_order_logic/set_inserter.hpp \
    first_order_logic/term_generator.hpp \
    first_order_logic/term.hpp \
    propositional_logic/deduction_tree.hpp \
    propositional_logic/proposition.hpp \
    propositional_logic/propositional_combine.hpp \
    propositional_logic/propositional_letter.hpp \
    propositional_logic/resolution_method.hpp \
    first_order_logic/predicate.hpp \
    first_order_logic/praser.hpp \
    first_order_logic/proof_tree.hpp

OTHER_FILES += \
    theorem_prover.pro.user \
    LICENSE \
    README.md

