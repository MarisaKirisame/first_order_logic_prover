TEMPLATE = app
CONFIG += console
CONFIG -= app_bundle
CONFIG -= qt
QMAKE_CXXFLAGS += -std=c++1y -stdlib=libc++ -ftemplate-backtrace-limit=0
SOURCES += main.cpp
LIBS += -lboost_unit_test_framework
HEADERS += \
    test.hpp \
    forward/first_order_logic.hpp \
    first_order_logic.hpp \
    TMP.hpp \
    satisfiability.hpp \
    sentence/atomic_sentence.hpp \
    sentence/constant.hpp \
    sentence/converter.hpp \
    sentence/function.hpp \
    sentence/predicate.hpp \
    sentence/sentence.hpp \
    sentence/sentence_helper.hpp \
    sentence/sentence_operations.hpp \
    sentence/variable.hpp \
    sentence/substitution.hpp \
    sentence/term.hpp \
    sentence/definite_clause.hpp \
    sentence/parser.hpp \
    FOL/gentzen_system.hpp \
    FOL/knowledge_base.hpp \
    FOL/proof_tree.hpp \
    FOL/resolution.hpp \
    SAT/DPLL.hpp \
    SAT/WALKSAT.hpp \
    sentence/CNF.hpp \
    FOL/term_generator.hpp
OTHER_FILES += \
    theorem_prover.pro.user \
    LICENSE \
    README.md
INCLUDEPATH += GitSource/Idionne/hana/include
PRECOMPILED_HEADER = $$HEADERS
QMAKE_LFLAGS += -stdlib=libc++
