#ifndef AIGER_HPP
#define AIGER_HPP

#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdarg>
#include <cstdint>
#include <fstream>
#include <functional>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace aiger_cxx {

//----------------------------------------------------------------------
// Basic literals and helper functions
//----------------------------------------------------------------------

constexpr unsigned AIGER_FALSE = 0;
constexpr unsigned AIGER_TRUE = 1;

inline bool isConstant(unsigned lit)
{
  return lit == AIGER_FALSE || lit == AIGER_TRUE;
}

inline unsigned aiger_sign(unsigned lit) { return lit & 1; }

inline unsigned aiger_strip(unsigned lit) { return lit & ~1U; }

inline unsigned aiger_not(unsigned lit) { return lit ^ 1; }

inline unsigned aiger_var2lit(unsigned var) { return var << 1; }

inline unsigned aiger_lit2var(unsigned lit) { return lit >> 1; }

//----------------------------------------------------------------------
// Modes for I/O
//----------------------------------------------------------------------

enum class Mode
{
  Binary,
  Ascii,
  Stripped
};

//----------------------------------------------------------------------
// AigerType: tracks the role and index for each variable.
// This corresponds to the original C struct 'aiger_type'.
//----------------------------------------------------------------------
struct AigerType
{
  bool input = false;
  bool latch = false;
  bool isAnd = false;  // renamed from 'and' because 'and' is a keyword.
  bool mark = false;
  bool onstack = false;
  unsigned idx =
      0;  // index into the corresponding vector (inputs, latches, or ands)
};

//----------------------------------------------------------------------
// Data structures for the circuit
//----------------------------------------------------------------------

struct AigerAnd
{
  unsigned lhs;   // left-hand side literal (even number)
  unsigned rhs0;  // first operand literal
  unsigned rhs1;  // second operand literal
};

struct AigerSymbol
{
  unsigned lit;                // literal
  unsigned next;               // for latches: next state literal
  unsigned reset;              // for latches: reset literal (optional)
  std::vector<unsigned> lits;  // for justice: vector of literals
  std::string name;            // optional symbolic name
};

//----------------------------------------------------------------------
// The main AIGER circuit class
//----------------------------------------------------------------------

class AigerReader;
class Aiger
{
 protected:
  // The vector that maps each variable (by index) to its type information.
  std::vector<AigerType> types;

  // Circuit parameters (maxlit = 2*maxvar + 1)
  unsigned maxvar = 0;

  // Vectors of symbols for different types
  std::vector<AigerSymbol> inputs;
  std::vector<AigerSymbol> latches;
  std::vector<AigerSymbol> outputs;
  std::vector<AigerSymbol> bad;
  std::vector<AigerSymbol> constraints;
  std::vector<AigerSymbol> justice;
  std::vector<AigerSymbol> fairness;
  std::vector<AigerAnd> ands;
  std::vector<std::string> comments;

 public:
  static constexpr const char * VERSION = "1.9";

  // Constructors/Destructor use default RAII
  Aiger() = default;
  ~Aiger() = default;

  // Accessors
  const std::vector<AigerSymbol>& getInputs() const { return inputs; }
  const std::vector<AigerSymbol>& getLatches() const { return latches; }
  const std::vector<AigerSymbol>& getOutputs() const { return outputs; }
  const std::vector<AigerSymbol>& getBad() const { return bad; }
  const std::vector<AigerSymbol>& getConstraints() const { return constraints; }
  const std::vector<AigerSymbol>& getJustice() const { return justice; }
  const std::vector<AigerSymbol>& getFairness() const { return fairness; }
  const std::vector<AigerAnd>& getAnds() const { return ands; }
  const std::vector<std::string>& getComments() const { return comments; }

  void clearOutputs() { outputs.clear(); }
  unsigned nextUnusedLiteral() const { return ((maxvar<<1) + 2) ;}

  //----------------------------------------------------------------------
  // API to add components
  //----------------------------------------------------------------------

  void addInput(unsigned lit, const std::string & name = "");
  void addLatch(unsigned lit,
                unsigned next,
                const std::string & name = "",
                unsigned reset = 0);

  void addAnd(unsigned lhs, unsigned rhs0, unsigned rhs1);

  // Adds a reset value to a latch.
  // Precondition: `reset` must be either 0, 1, or equal to `lit`.
  // It updates the reset field for the latch symbol corresponding to `lit`.
  void addReset(unsigned lit, unsigned reset);

  // Adds an output symbol to the circuit.
  // 'lit' is the literal for the output, and 'name' is an optional symbolic
  // name.
  void addOutput(unsigned lit, const std::string & name);

  // Adds a 'bad' state symbol.
  void addBad(unsigned lit, const std::string & name);

  // Adds an invariant constraint symbol.
  void addConstraint(unsigned lit, const std::string & name);

  // Adds a justice constraint symbol. The 'lits' array is copied into a vector.
  void addJustice(unsigned size,
                  const unsigned * lits,
                  const std::string & name);

  // Adds a fairness constraint symbol.
  void addFairness(unsigned lit, const std::string & name);

  void addComment(const std::string & comment);

  //----------------------------------------------------------------------
  // Consistency check (simplified)
  //----------------------------------------------------------------------

 public:
  bool literalDefined(unsigned lit) const;

 protected:
  void checkNextDefined() const;

  void checkRightHandSideDefined(const AigerAnd & gate, unsigned rhs) const;
  void checkRightHandSidesDefined() const;
  void checkOutputsDefined() const;
  void checkBadDefined() const;
  void checkConstraintsDefined() const;
  void checkFairnessDefined() const;
  void checkJusticeDefined() const;

  /// Checks for cycles among AND-gates in the circuit.
  /// Throws a runtime_error if a cycle is detected.
  void checkForCycles();

 public:
  // Returns an empty string if the circuit is consistent, or an error message
  // if not.
  std::string check();

  //----------------------------------------------------------------------
  // Reencode the circuit (simplified version)
  //----------------------------------------------------------------------

 public:
  // Returns the maximum literal among inputs and latches.
  unsigned maxInputOrLatch() const;

  // Checks whether the circuit is reencoded.
  // Returns true if the AND–gate literals follow the expected ordering.
  bool isReencoded() const;

  // The main reencoding function.
  // This method reassigns literals so that inputs and latches come first,
  // followed by a topologically sorted order of AND gates.
  void reencode();

protected:
  // Helper that mimics aiger_new_code: assigns new code values for a given
  // variable.
  void newCode(unsigned var, unsigned & curNew, std::vector<unsigned> & code);

  // Recursively reencodes the literal.
  // 'curNew' is the next free code value.
  // 'code' is a vector (indexed by literal) that holds the new code;
  // 'stack' is a DFS stack used during reencoding.
  unsigned reencodeLit(unsigned lit,
                       unsigned & curNew,
                       std::vector<unsigned> & code,
                       std::vector<unsigned> & stack);


  //----------------------------------------------------------------------
  // Retrieve a symbol name for an input or latch literal.
  //----------------------------------------------------------------------

  std::string getSymbol(unsigned lit) const;

  //----------------------------------------------------------------------
  // Fast lookup functions using the types vector.
  //----------------------------------------------------------------------

  // Returns a pointer to the input symbol for lit, or nullptr if lit is not an
  // input.
  const AigerSymbol * isInput(unsigned lit) const;

  // Returns a pointer to the latch symbol for lit, or nullptr if lit is not a
  // latch.
  const AigerSymbol * isLatch(unsigned lit) const;

  // Returns a pointer to the AND gate for lit, or nullptr if lit is not an AND
  // gate.
  const AigerAnd * isAnd(unsigned lit) const;

 protected:
  // Helper: given a literal, returns a const reference to its AigerType.
  // (This corresponds to the original aiger_lit2type.)
  const AigerType & lit2type(unsigned lit) const;

  // Resize the types vector as needed and update maxvar.
  void updateMaxvar(unsigned lit);

 protected:
  // Checks whether the literal 'lit' is already defined.
  // Returns an empty string if not defined; otherwise an error message.
  std::string alreadyDefined(unsigned lit, const AigerReader & reader) const;

 protected:
  // Reads the AIGER header (including symbol counts and symbol table entries)
  // from the input via 'reader'. Returns an empty string on success, or an
  // error message on failure.
  std::string readHeader(AigerReader & reader);

  // Reads the ASCII portion for AND gates from the input via reader.
  // Returns an empty string on success or an error message otherwise.
  std::string readAscii(AigerReader & reader);

  // Reads the binary-encoded AND gates from the reader.
  // Returns an empty string on success, or an error message.
  std::string readBinary(AigerReader & reader);

  // Reads comment lines from the reader.
  // Assumes that the current character (reader.ch) is '\n'.
  // Returns an empty string on success or an error message.
  std::string readComments(AigerReader & reader);

  // Reads the symbol table and comment section from the input stream (via
  // reader) and populates the circuit's symbol vectors. Returns an empty string
  // on success; otherwise, an error message.
  std::string readSymbolsAndComments(AigerReader & reader);

 public:
  /// Reads the entire circuit from an input stream.
  /// Returns an empty string on success or an error message on failure.
  std::string readFromStream(std::istream & in);

  /// Reads the circuit from a file (by filename).
  /// Returns an empty string on success or an error message on failure.
  std::string readFromFile(const std::string & fileName);

 protected:
  // Writes a single character to out.
  int defaultPut(std::ostream & out, char ch) const;

  // Writes a string to out.
  int putS(std::ostream & out, const std::string & s) const;

  // Writes an unsigned integer as a string to out.
  int putU(std::ostream & out, unsigned u) const;

  // Writes a delta-encoded unsigned number.
  int writeDelta(std::ostream & out, unsigned delta) const;

  // Writes the header line.
  int writeHeader(std::ostream & out,
                  const std::string & formatString,
                  bool compactInputsAndLatches) const;

  // --- Symbol Table Helpers ---

  bool haveAtLeastOneSymbolAux(const std::vector<AigerSymbol> & symbols) const;

  bool haveAtLeastOneSymbol() const;

  int writeSymbolsAux(std::ostream & out,
                      const std::string & typeLabel,
                      const std::vector<AigerSymbol> & symbols) const;

  int writeSymbols(std::ostream & out) const;

  // Writes symbols to stream.
  bool writeSymbolsToStream(std::ostream & out) const;

  // --- Comments ---

  int writeComments(std::ostream & out) const;

  bool writeCommentsToStream(std::ostream & out) const;
  // --- ASCII and Binary Output ---

  int writeAscii(std::ostream & out);

  int writeBinary(std::ostream & out);

 public:
  // --- Strip Symbols and Comments ---


  unsigned deleteSymbols(std::vector<AigerSymbol> & symbols);
  unsigned deleteComments();
  unsigned stripSymbolsAndComments();

  // --- Generic Write ---

  // Writes the entire circuit to stream in the specified mode.
  // Returns true on success, false on failure.
  bool writeGeneric(Mode mode, std::ostream & out);

  // Writes the circuit to a stream.
  bool writeToStream(Mode mode, std::ostream & out);

  // Writes the circuit to a file.
  bool writeToFile(Mode mode, const std::string & filename);

  // Writes the circuit to a string.
  std::string writeToString(Mode mode);
};


}  // namespace aiger

#endif  // AIGER_HPP
