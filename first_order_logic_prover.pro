TEMPLATE = app
CONFIG += console
CONFIG -= app_bundle
CONFIG -= qt
QMAKE_CXXFLAGS += -std=c++1y -ftemplate-backtrace-limit=0
SOURCES += main.cpp
LIBS += -lboost_unit_test_framework
HEADERS += \
    function.hpp \
    predicate.hpp \
    proof_tree.hpp \
    term_generator.hpp \
    test.hpp \
    gentzen_system.hpp \
    substitution.hpp \
    term.hpp \
    variable.hpp \
    constant.hpp \
    definite_clause.hpp \
    sentence.hpp \
    knowledge_base.hpp \
    parser.hpp \
    function_output_iterator.hpp \
    forward/first_order_logic.hpp \
    first_order_logic.hpp \
    resolution.hpp \
    atomic_sentence.hpp \
    sentence_helper.hpp \
    TMP.hpp \
    converter.hpp \
    DPLL.hpp \
    WALKSAT.hpp \
    sentence_operations.hpp \
    CNF.hpp \
    satisfiability.hpp
OTHER_FILES += \
    theorem_prover.pro.user \
    LICENSE \
    README.md

PRECOMPILED_HEADER = $$HEADERS
