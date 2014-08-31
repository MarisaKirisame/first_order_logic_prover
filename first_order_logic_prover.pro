TEMPLATE = app
CONFIG += console
CONFIG -= app_bundle
CONFIG -= qt
QMAKE_CXXFLAGS += -std=c++1y
SOURCES += main.cpp
LIBS += -lboost_unit_test_framework
HEADERS += \
    first_order_logic.hpp \
    function.hpp \
    praser.hpp \
    predicate.hpp \
    proof_tree.hpp \
    term_generator.hpp \
    term.hpp \
    test.hpp \
    gentzen_system.hpp \
    substitution.hpp

OTHER_FILES += \
    theorem_prover.pro.user \
    LICENSE \
    README.md

