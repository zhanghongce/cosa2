#include "aiger.hpp"

namespace aiger_cxx {


//----------------------------------------------------------------------
// A simple AigerReader class using C++ streams
//----------------------------------------------------------------------

//---------------------------------------------------------------------
// Helper: Check if a string has a given suffix.
//---------------------------------------------------------------------
inline bool hasSuffix(const std::string & str, const std::string & suffix)
{
  return (str.size() >= suffix.size()
          && str.compare(str.size() - suffix.size(), suffix.size(), suffix)
                 == 0);
}

// Helper: Format a string using printf–style formatting.
static std::string vformat(const char * fmt, va_list args)
{
  va_list argsCopy;
  va_copy(argsCopy, args);
  int len = std::vsnprintf(nullptr, 0, fmt, argsCopy);
  va_end(argsCopy);
  if (len < 0) throw std::runtime_error("String formatting error");
  std::vector<char> buf(len + 1);
  std::vsnprintf(buf.data(), buf.size(), fmt, args);
  return std::string(buf.data(), len);
}

static std::string format(const char * fmt, ...)
{
  va_list args;
  va_start(args, fmt);
  std::string s = vformat(fmt, args);
  va_end(args);
  return s;
}

// Returns an error string formatted with one unsigned value.
static std::string aiger_error_u(const char * s, unsigned u)
{
  return format(s, u);
}

// Returns an error string formatted with two unsigned values.
static std::string aiger_error_uu(const char * s, unsigned a, unsigned b)
{
  return format(s, a, b);
}

// Returns an error string formatted with an unsigned and a C-string.
static std::string aiger_error_us(const char * s, unsigned a, const char * b)
{
  return format(s, a, b);
}

// Returns an error string formatted with an unsigned, a C-string, and another
// unsigned.
static std::string aiger_error_usu(const char * s,
                                   unsigned a,
                                   const char * t,
                                   unsigned b)
{
  return format(s, a, t, b);
}


//---------------------------------------------------------------------
// AigerReader: a modern replacement for the aiger_reader struct.
//---------------------------------------------------------------------
class AigerReader
{
  friend class Aiger;
 protected:
  // Construct from an input stream.
  explicit AigerReader(std::istream & in)
      : ch(' '),   // initial dummy value
        lineno(1),
        charno(0),
        linenoAtLastTokenStart(1),
        doneWithHeader(false),
        looksLikeAAG(true),
        mode(Mode::Ascii),
        maxvar(0),
        inputs(0),
        latches(0),
        outputs(0),
        ands(0),
        bad(0),
        constraints(0),
        justice(0),
        fairness(0),
        inStream(in)
  {  }

  // Read next character from stream.
  int nextCh()
  {
    int res = inStream.get();
    // If previous char was whitespace and current is non-whitespace, update
    // token start.
    if (std::isspace(ch) && !std::isspace(res)) linenoAtLastTokenStart = lineno;
    ch = res;
    if (doneWithHeader && looksLikeAAG) {
      if (!std::isspace(res) && !std::isdigit(res) && res != EOF)
        looksLikeAAG = false;
    }
    if (res == '\n') ++lineno;
    if (res != EOF) ++charno;
    return res;
  }

  // Read a number (assumes current ch is a digit).
  unsigned readNumber()
  {
    if (!std::isdigit(ch))
      throw std::runtime_error("Expected digit at line "
                               + std::to_string(lineno));
    unsigned res = ch - '0';
    while (std::isdigit(nextCh())) res = 10 * res + (ch - '0');
    return res;
  }

  // Read an unsigned literal with an expected delimiter.
  // If followedBy is nonzero, the current character must equal it.
  // Returns an error message (empty string if successful).
  std::string readLiteral(const std::string & context,
                          unsigned & res,
                          char expectedFollowedBy,
                          char * followedByPtr = nullptr)
  {
    assert(expectedFollowedBy == ' ' || expectedFollowedBy == '\n'
           || !expectedFollowedBy);

    if (!std::isdigit(ch)) return errorUs(lineno, context);
    res = readNumber();
    if (expectedFollowedBy == ' ') {
      if (ch != ' ')
        return errorUsu(linenoAtLastTokenStart, context, res, "expected space");
    } else if (expectedFollowedBy == '\n') {
      if (ch != '\n')
        return errorUsu(
            linenoAtLastTokenStart, context, res, "expected newline");
    } else if (!expectedFollowedBy) {
      if (ch != '\n' && ch != ' ')
        return errorUsu(
            linenoAtLastTokenStart, context, res, "expected space or newline");
    }
    if (followedByPtr) *followedByPtr = ch;
    nextCh();  // consume the delimiter
    return "";
  }
  // Reads a delta-encoded unsigned number from the input.
  // On success, sets 'result' and returns an empty string.
  // On error, returns an error message.
  std::string readDelta(unsigned & result)
  {
    // If current character is EOF, report unexpected end-of-file.
    if (ch == EOF)
      return aiger_error_u("character %u: unexpected end of file", charno);

    unsigned i = 0;
    result = 0;
    // Use current character as unsigned.
    unsigned char current = static_cast<unsigned char>(ch);
    // Save starting character number for error messages.
    unsigned startCharNo = charno;

    // While the MSB is set, continue reading the delta.
    while (current & 0x80) {
      // Ensure that an unsigned is 4 bytes.
      static_assert(sizeof(unsigned) == 4, "Expected unsigned to be 4 bytes");

      if (i == 5)
        return aiger_error_u("character %u: invalid code", startCharNo);

      result |= (current & 0x7F) << (7 * i);
      i++;
      nextCh();  // Advance to the next character.
      if (ch == EOF)
        return aiger_error_u("character %u: unexpected end of file", charno);

      current = static_cast<unsigned char>(ch);
    }

    // If we read 5 bytes and the final byte is too large, it's an error.
    if (i == 5 && current >= 8)
      return aiger_error_u("character %u: invalid code", startCharNo);

    result |= current << (7 * i);
    nextCh();  // Consume the last character.

    return "";  // Success.
  }

 public:
  // Appends the character 'ch' to the buffer.
  void pushChar(char ch) { buffer.push_back(ch); }

  // Buffer for accumulating strings (for comments, symbols, etc.).
  std::string buffer;
  // Public fields (corresponding to the original aiger_reader struct).
  int ch;
  unsigned lineno;
  unsigned charno;
  unsigned linenoAtLastTokenStart;
  bool doneWithHeader;
  bool looksLikeAAG;
  Mode mode;
  unsigned maxvar;
  unsigned inputs, latches, outputs, ands, bad, constraints, justice, fairness;

  // (We no longer need explicit buffer size variables because std::string
  // manages that.)
 private:
  // Input stream.
  std::istream & inStream;
  // Helper error functions:
  std::string errorUs(unsigned line, const std::string & context) const
  {
    return "line " + std::to_string(line) + ": " + context;
  }
  std::string errorUsu(unsigned line,
                       const std::string & context,
                       unsigned value,
                       const std::string & msg) const
  {
    return "line " + std::to_string(line) + ": " + msg + " after " + context
           + " " + std::to_string(value);
  }
};

// A helper to “fit” a vector to at least newSize elements.
template <typename T>
void fitVector(std::vector<T> & vec, size_t newSize)
{
  if (vec.size() < newSize) vec.resize(newSize);
}

void Aiger::addInput(unsigned lit, const std::string & name)
{
  if (lit < 2 || aiger_sign(lit))
    throw std::invalid_argument("Invalid input literal");
  updateMaxvar(lit);
  unsigned var = aiger_lit2var(lit);
  if (types[var].input || types[var].latch || types[var].isAnd)
    throw std::invalid_argument("Literal already defined");
  types[var].input = true;
  types[var].idx = inputs.size();
  inputs.push_back({ lit, 0, 0, {}, name });
}


void Aiger::addLatch(unsigned lit,
              unsigned next,
              const std::string & name,
              unsigned reset)
{
  if (lit < 2 || aiger_sign(lit))
    throw std::invalid_argument("Invalid latch literal");
  updateMaxvar(lit);
  updateMaxvar(next);
  updateMaxvar(reset);
  unsigned var = aiger_lit2var(lit);
  if (types[var].input || types[var].latch || types[var].isAnd)
    throw std::invalid_argument("Literal already defined");
  types[var].latch = true;
  types[var].idx = latches.size();
  latches.push_back({ lit, next, reset, {}, name });
}

void Aiger::addAnd(unsigned lhs, unsigned rhs0, unsigned rhs1)
{
  if (lhs < 2 || aiger_sign(lhs))
    throw std::invalid_argument("Invalid AND literal");
  updateMaxvar(lhs);
  updateMaxvar(rhs0);
  updateMaxvar(rhs1);
  unsigned var = aiger_lit2var(lhs);
  if (types[var].input || types[var].latch || types[var].isAnd)
    throw std::invalid_argument("Literal already defined");
  types[var].isAnd = true;
  types[var].idx = ands.size();
  ands.push_back({ lhs, rhs0, rhs1 });
}

// Adds a reset value to a latch.
// Precondition: `reset` must be either 0, 1, or equal to `lit`.
// It updates the reset field for the latch symbol corresponding to `lit`.
void Aiger::addReset(unsigned lit, unsigned reset)
{
  // Validate reset value.
  if (!(reset <= 1 || reset == lit))
    throw std::invalid_argument(
        "Invalid reset value: must be 0, 1, or equal to lit");
  // Validate literal.
  if (lit == 0 || aiger_sign(lit))
    throw std::invalid_argument(
        "Invalid literal for latch (must be positive even)");
  // Ensure the literal is imported/registered.
  // (This might update the types vector; here we assume updateMaxvar is
  // called elsewhere.)
  unsigned var = aiger_lit2var(lit);
  if (var >= types.size() || !types[var].latch)
    throw std::logic_error("Literal is not defined as a latch");
  unsigned idx = types[var].idx;
  if (idx >= latches.size())
    throw std::logic_error("Latch index out of bounds");
  latches[idx].reset = reset;
}

// Adds an output symbol to the circuit.
// 'lit' is the literal for the output, and 'name' is an optional symbolic
// name.
void Aiger::addOutput(unsigned lit, const std::string & name)
{
  // Update maximum variable index if needed.
  updateMaxvar(lit);
  // Optionally, you could "import" the literal here.
  AigerSymbol sym{};  // All fields zero/empty by default.
  sym.lit = lit;
  sym.name = name;  // std::string makes a copy of the given name.
  outputs.push_back(sym);
}

// Adds a 'bad' state symbol.
void Aiger::addBad(unsigned lit, const std::string & name)
{
  updateMaxvar(lit);
  // Optionally, if you want to record the literal in the type info, do so
  // here.
  AigerSymbol sym{};  // zero-initialized
  sym.lit = lit;
  sym.name = name;
  bad.push_back(sym);
}

// Adds an invariant constraint symbol.
void Aiger::addConstraint(unsigned lit, const std::string & name)
{
  updateMaxvar(lit);
  AigerSymbol sym{};
  sym.lit = lit;
  sym.name = name;
  constraints.push_back(sym);
}

// Adds a justice constraint symbol. The 'lits' array is copied into a vector.
void Aiger::addJustice(unsigned size,
                const unsigned * lits,
                const std::string & name)
{
  AigerSymbol sym{};
  sym.lits.resize(size);
  for (unsigned i = 0; i < size; i++) {
    updateMaxvar(lits[i]);
    sym.lits[i] = lits[i];
  }
  sym.name = name;
  justice.push_back(sym);
}

// Adds a fairness constraint symbol.
void Aiger::addFairness(unsigned lit, const std::string & name)
{
  updateMaxvar(lit);
  AigerSymbol sym{};
  sym.lit = lit;
  sym.name = name;
  fairness.push_back(sym);
}


void Aiger::addComment(const std::string & comment)
{
  // Comments should not contain newline characters.
  if (comment.find('\n') != std::string::npos)
    throw std::invalid_argument("Comment cannot contain newline characters");
  comments.push_back(comment);
}


bool Aiger::literalDefined(unsigned lit) const
{
  unsigned var = aiger_lit2var(lit);
  // For constant literals, we assume they are always defined.
  if (var == 0) return true;
  // Ensure our types vector is large enough.
  if (var >= types.size()) return false;
  const AigerType & type = types[var];
  return type.isAnd || type.input || type.latch;
}

void Aiger::checkNextDefined() const
{
  for (const auto & latchSym : latches) {
    unsigned latch = latchSym.lit;
    unsigned next = latchSym.next;
    // Latch literals must not be signed.
    if (aiger_sign(latch))
      throw std::logic_error("checkNextDefined: latch literal is signed");
    unsigned var = aiger_lit2var(latch);
    if (var >= types.size() || !types[var].latch)
      throw std::logic_error(
          "checkNextDefined: literal does not have latch type");
    if (!literalDefined(next)) {
      throw std::runtime_error("Next state function " + std::to_string(next)
                               + " of latch " + std::to_string(latch)
                               + " undefined");
    }
  }
}

void Aiger::checkRightHandSideDefined(const AigerAnd & gate, unsigned rhs) const
{
  if (!literalDefined(rhs)) {
    throw std::runtime_error("Literal " + std::to_string(rhs)
                             + " in AND gate " + std::to_string(gate.lhs)
                             + " undefined");
  }
}
void Aiger::checkRightHandSidesDefined() const
{
  for (const auto & gate : ands) {
    checkRightHandSideDefined(gate, gate.rhs0);
    checkRightHandSideDefined(gate, gate.rhs1);
  }
}
void Aiger::checkOutputsDefined() const
{
  for (const auto & outputSym : outputs) {
    unsigned output = aiger_strip(outputSym.lit);
    // If output is constant (<= 1) we consider it defined.
    if (output <= 1) continue;
    if (!literalDefined(output))
      throw std::runtime_error("Output " + std::to_string(output)
                               + " undefined");
  }
}
void Aiger::checkBadDefined() const
{
  for (const auto & badSym : bad) {
    unsigned badLit = aiger_strip(badSym.lit);
    if (badLit <= 1) continue;
    if (!literalDefined(badLit))
      throw std::runtime_error("Bad state literal " + std::to_string(badLit)
                               + " undefined");
  }
}
void Aiger::checkConstraintsDefined() const
{
  for (const auto & consSym : constraints) {
    unsigned cons = aiger_strip(consSym.lit);
    if (cons <= 1) continue;
    if (!literalDefined(cons))
      throw std::runtime_error("Constraint literal " + std::to_string(cons)
                               + " undefined");
  }
}
void Aiger::checkFairnessDefined() const
{
  for (const auto & fairSym : fairness) {
    unsigned fair = aiger_strip(fairSym.lit);
    if (fair <= 1) continue;
    if (!literalDefined(fair))
      throw std::runtime_error("Fairness literal " + std::to_string(fair)
                               + " undefined");
  }
}
void Aiger::checkJusticeDefined() const
{
  for (const auto & justSym : justice) {
    for (unsigned lit : justSym.lits) {
      unsigned jLit = aiger_strip(lit);
      if (jLit <= 1) continue;
      if (!literalDefined(jLit))
        throw std::runtime_error("Justice literal " + std::to_string(jLit)
                                 + " undefined");
    }
  }
}

/// Checks for cycles among AND-gates in the circuit.
/// Throws a runtime_error if a cycle is detected.
void Aiger::checkForCycles()
{
  // We'll use a DFS stack where a nonzero value represents a node (variable
  // index) and a zero value acts as a marker for postorder processing.
  std::vector<unsigned> stack;

  // Iterate over variable indices from 1 up to maxvar.
  // (Index 0 is reserved for the constant.)
  for (unsigned i = 1; i <= maxvar; i++) {
    if (i >= types.size()) continue;
    AigerType & t = types[i];
    // Only process nodes corresponding to AND gates that haven't been marked.
    if (!t.isAnd || t.mark) continue;

    // Push the starting node onto the stack.
    stack.push_back(i);

    // Process the DFS.
    while (!stack.empty()) {
      unsigned j = stack.back();

      if (j != 0) {
        // Process a non-marker node.
        AigerType & curr = types[j];
        // If the node is already marked and still on the stack, a cycle is
        // found.
        if (curr.mark && curr.onstack)
          throw std::runtime_error("Cyclic definition for AND gate "
                                   + std::to_string(j));

        // If this node is not an AND or has already been processed, pop and
        // continue.
        if (!curr.isAnd || curr.mark) {
          stack.pop_back();
          continue;
        }

        // Mark the node (prefix action) and push a zero marker
        // to denote that after processing its children we must clear its
        // onstack flag.
        curr.mark = true;
        curr.onstack = true;
        stack.push_back(0);

        // Retrieve the AND gate corresponding to this node.
        if (curr.idx >= ands.size())
          throw std::logic_error("Invalid index in AND gates vector");
        const AigerAnd & gate = ands[curr.idx];

        // Get the variables (child nodes) from the right-hand side literals.
        unsigned tmp = aiger_lit2var(gate.rhs0);
        if (tmp != 0) stack.push_back(tmp);
        tmp = aiger_lit2var(gate.rhs1);
        if (tmp != 0) stack.push_back(tmp);
      } else {
        // Postfix processing: a marker (0) encountered.
        // According to the original code, we then pop two items:
        // the marker and the node associated with it.
        if (stack.size() < 2)
          throw std::logic_error("Stack underflow during cycle check");
        // Remove the marker.
        stack.pop_back();
        unsigned node = stack.back();
        assert(node);  // should not be 0
        stack.pop_back();
        if (node >= types.size())
          throw std::logic_error("Invalid node index in cycle check");
        AigerType & nodeType = types[node];
        if (!nodeType.mark || !nodeType.onstack)
          throw std::logic_error("Inconsistent state in cycle check");
        // Clear the onstack flag after all descendants have been processed.
        nodeType.onstack = false;
      }
    }
  }
}  // end of checkForCycles

// Returns an empty string if the circuit is consistent, or an error message
// if not.
std::string Aiger::check()
{
  try {
    // Call all checking functions.
    checkNextDefined();
    checkOutputsDefined();
    checkBadDefined();
    checkConstraintsDefined();
    checkJusticeDefined();
    checkFairnessDefined();
    checkRightHandSidesDefined();
    checkForCycles();
    return "";
  }
  catch (const std::exception & ex) {
    return ex.what();
  }
} // end of Aiger::check()


// Returns the maximum literal among inputs and latches.
unsigned Aiger::maxInputOrLatch() const
{
  unsigned res = 0;
  for (const auto & sym : inputs) {
    unsigned tmp = sym.lit;
    assert(!aiger_sign(tmp));
    if (tmp > res) res = tmp;
  }
  for (const auto & sym : latches) {
    unsigned tmp = sym.lit;
    assert(!aiger_sign(tmp));
    if (tmp > res) res = tmp;
  }
  return res;
}

// Checks whether the circuit is reencoded.
// Returns true if the AND–gate literals follow the expected ordering.
bool Aiger::isReencoded() const
{
  unsigned max_val = 0;
  // For inputs:
  for (const auto & sym : inputs) {
    max_val += 2;
    unsigned tmp = sym.lit;
    if (max_val != tmp)
      return false;
  }
  // For latches:
  for (const auto & sym : latches) {
    max_val += 2;
    unsigned tmp = sym.lit;
    if (max_val != tmp)
      return false;
  }
  unsigned lhs_expected = maxInputOrLatch() + 2;
  for (const auto & gate : ands) {
    if (gate.lhs <= max_val)
      return false;
    if (gate.lhs != lhs_expected)
      return false;
    if (gate.lhs < gate.rhs0)
      return false;
    if (gate.rhs0 < gate.rhs1)
      return false;
    lhs_expected += 2;
  }
  return true;
}  // end of isReencoded

// Helper that mimics aiger_new_code: assigns new code values for a given
// variable.
void Aiger::newCode(unsigned var, unsigned & curNew, std::vector<unsigned> & code)
{
  unsigned lit = aiger_var2lit(var);
  assert(code[lit] == 0);
  unsigned res = curNew;
  code[lit] = res;
  code[lit + 1] = res + 1;
  curNew += 2;
}

// Recursively reencodes the literal.
// 'curNew' is the next free code value.
// 'code' is a vector (indexed by literal) that holds the new code;
// 'stack' is a DFS stack used during reencoding.
unsigned Aiger::reencodeLit(unsigned lit,
                     unsigned & curNew,
                     std::vector<unsigned> & code,
                     std::vector<unsigned> & stack)
{
  if (lit < 2) return lit;
  unsigned res = code[lit];
  if (res != 0) return res;

  unsigned var = aiger_lit2var(lit);
  assert(var <= maxvar);
  AigerType & type = types[var];

  if (type.isAnd) {
    // Clear the stack for this invocation.
    stack.clear();
    stack.push_back(var);

    while (!stack.empty()) {
      unsigned topVal = stack.back();
      stack.pop_back();

      if (topVal != 0) {
        // If new code for 'topVal' is already assigned, skip.
        if (code[aiger_var2lit(topVal)] != 0) continue;
        assert(topVal <= maxvar);
        AigerType & curType = types[topVal];
        if (curType.onstack) continue;
        curType.onstack = true;
        // Push a marker (0) after the current node.
        stack.push_back(topVal);
        stack.push_back(0);

        // Retrieve the AND gate corresponding to 'topVal'
        assert(curType.isAnd);
        assert(curType.idx < ands.size());
        const AigerAnd & gate = ands[curType.idx];
        // Get child variables from the right–hand side literals.
        unsigned child0 = aiger_lit2var(gate.rhs0);
        unsigned child1 = aiger_lit2var(gate.rhs1);
        if (child0 < child1) std::swap(child0, child1);
        assert(child0 >= child1); /* smaller child first */
        // Push children if nonzero and not inputs/latches and not already on
        // stack.
        if (child0 && !types[child0].input && !types[child0].latch
            && !types[child0].onstack)
          stack.push_back(child0);
        if (child1 && !types[child1].input && !types[child1].latch
            && !types[child1].onstack)
          stack.push_back(child1);
      } else {
        // Marker encountered: pop the associated node and assign new code.
        assert(!stack.empty());
        unsigned node = stack.back();
        stack.pop_back();
        assert(code[aiger_var2lit(node)] == 0);
        AigerType & nodeType = types[node];
        assert(nodeType.onstack);
        nodeType.onstack = false;
        newCode(node, curNew, code);
      }
    }
  } else {
    // For inputs or latches, the new code is the same as the original.
    assert(type.input || type.latch);
    assert(lit < curNew);
    code[lit] = lit;
    code[aiger_not(lit)] = aiger_not(lit);
  }
  assert(code[lit] != 0);
  return code[lit];
}  // end of reencodeLit

// The main reencoding function.
// This method reassigns literals so that inputs and latches come first,
// followed by a topologically sorted order of AND gates.
void Aiger::reencode()
{
  // (Assume no error has been set.)
  if (isReencoded()) return;

  // Allocate a code vector of size: 2*(maxvar + 1)
  unsigned size_code = 2 * (maxvar + 1);
  if (size_code < 2) size_code = 2;
  std::vector<unsigned> code(size_code, 0);
  code[1] = 1;  // (not used)

  unsigned curNew = 2;

  // Recode inputs.
  for (auto & sym : inputs) {
    unsigned old = sym.lit;
    code[old] = curNew;
    code[old + 1] = curNew + 1;
    curNew += 2;
  }
  // Recode latches.
  for (auto & sym : latches) {
    unsigned old = sym.lit;
    code[old] = curNew;
    code[old + 1] = curNew + 1;
    curNew += 2;
  }

  // Prepare a DFS stack for reencodeLit.
  std::vector<unsigned> dfsStack;

  // Reencode 'next' and 'reset' fields for latches.
  for (auto & sym : latches) {
    unsigned old = sym.next;
    sym.next = reencodeLit(old, curNew, code, dfsStack);
    old = sym.reset;
    sym.reset = reencodeLit(old, curNew, code, dfsStack);
  }

  // Reencode outputs.
  for (auto & sym : outputs) {
    unsigned old = sym.lit;
    sym.lit = reencodeLit(old, curNew, code, dfsStack);
  }

  // Reencode bad states.
  for (auto & sym : bad) {
    unsigned old = sym.lit;
    sym.lit = reencodeLit(old, curNew, code, dfsStack);
  }

  // Reencode constraints.
  for (auto & sym : constraints) {
    unsigned old = sym.lit;
    sym.lit = reencodeLit(old, curNew, code, dfsStack);
  }

  // Reencode justice symbols.
  for (auto & sym : justice) {
    for (unsigned i = 0; i < sym.lits.size(); i++) {
      unsigned old = sym.lits[i];
      sym.lits[i] = reencodeLit(old, curNew, code, dfsStack);
    }
  }

  // Reencode fairness symbols.
  for (auto & sym : fairness) {
    unsigned old = sym.lit;
    sym.lit = reencodeLit(old, curNew, code, dfsStack);
  }

  // Reconstruct AND–gates.
  unsigned j = 0;
  for (unsigned i = 0; i < ands.size(); i++) {
    const AigerAnd & gate = ands[i];
    unsigned newLhs = code[gate.lhs];
    if (!newLhs) { 
      // if ANG gate is not in used, it seems that
      // it will have 0, so we should skip it
      continue;
    }
    unsigned newRhs0 = code[gate.rhs0];
    unsigned newRhs1 = code[gate.rhs1];
    // Place the gate at index j.
    if (newRhs0 < newRhs1)
      std::swap(newRhs0, newRhs1);
    assert(newLhs > newRhs0);
    assert(newRhs0 >= newRhs1);
    AigerAnd & gate_j = ands.at(j++);
    gate_j.lhs = newLhs;
    gate_j.rhs0 = newRhs0;
    gate_j.rhs1 = newRhs1;
  }
  ands.resize(j);

  // Sort the AND–gates by lhs.
  std::sort(
      ands.begin(), ands.end(), [](const AigerAnd & a, const AigerAnd & b) {
        return a.lhs < b.lhs;
      });

  // Reset types: for each variable from 1 to maxvar.
  for (unsigned i = 1; i <= maxvar; i++) {
    if (i < types.size()) {
      types[i].input = false;
      types[i].latch = false;
      types[i].isAnd = false;
      types[i].idx = 0;
    }
  }
  assert(curNew != 0);
  assert(maxvar >= aiger_lit2var(curNew - 1));
  maxvar = aiger_lit2var(curNew - 1);

  // Fix types for AND–gates.
  for (unsigned i = 0; i < ands.size(); i++) {
    unsigned var = aiger_lit2var(ands[i].lhs);
    if (var >= types.size()) {
      assert(false);  // should not happen
      types.resize(var + 1);
    }
    types[var].isAnd = true;
    types[var].idx = i;
  }

  // Fix types for inputs.
  for (unsigned i = 0; i < inputs.size(); i++) {
    AigerSymbol & sym = inputs[i];
    assert(sym.lit < code.size());
    sym.lit = code[sym.lit];
    unsigned var = aiger_lit2var(sym.lit);
    if (var >= types.size()) {
      assert(false);  // should not happen
      types.resize(var + 1);
    }
    types[var].input = true;
    types[var].idx = i;
  }

  // Fix types for latches.
  for (unsigned i = 0; i < latches.size(); i++) {
    AigerSymbol & sym = latches[i];
    sym.lit = code[sym.lit];
    unsigned var = aiger_lit2var(sym.lit);
    if (var >= types.size()) {
      assert(false);  // should not happen
      types.resize(var + 1);
    }
    types[var].latch = true;
    types[var].idx = i;
  }
  // 'code' and 'dfsStack' are automatically deallocated.
  assert(isReencoded());
  assert(check().empty());
}  // end of Aiger::reencode



//----------------------------------------------------------------------
// Retrieve a symbol name for an input or latch literal.
//----------------------------------------------------------------------

std::string Aiger::getSymbol(unsigned lit) const
{
  // Preconditions: lit must be non-zero and not signed.
  assert(lit != 0);
  assert(!aiger_sign(lit));
  unsigned var = aiger_lit2var(lit);
  assert(var <= maxvar);
  const AigerType & t = lit2type(lit);  // protected helper below
  if (t.input)
    return inputs[t.idx].name;
  else if (t.latch)
    return latches[t.idx].name;
  else
    return "";
}

//----------------------------------------------------------------------
// Fast lookup functions using the types vector.
//----------------------------------------------------------------------

// Returns a pointer to the input symbol for lit, or nullptr if lit is not an
// input.
const AigerSymbol * Aiger::isInput(unsigned lit) const
{
  const AigerType & t = lit2type(lit);
  if (!t.input) return nullptr;
  return &inputs[t.idx];
}

// Returns a pointer to the latch symbol for lit, or nullptr if lit is not a
// latch.
const AigerSymbol * Aiger::isLatch(unsigned lit) const
{
  const AigerType & t = lit2type(lit);
  if (!t.latch) return nullptr;
  return &latches[t.idx];
}

// Returns a pointer to the AND gate for lit, or nullptr if lit is not an AND
// gate.
const AigerAnd * Aiger::isAnd(unsigned lit) const
{
  const AigerType & t = lit2type(lit);
  if (!t.isAnd) return nullptr;
  return &ands[t.idx];
}

// Helper: given a literal, returns a const reference to its AigerType.
// (This corresponds to the original aiger_lit2type.)
const AigerType & Aiger::lit2type(unsigned lit) const
{
  unsigned var = aiger_lit2var(lit);
  assert(var <= maxvar);
  return types[var];
}

// Resize the types vector as needed and update maxvar.
void Aiger::updateMaxvar(unsigned lit)
{
  unsigned var = aiger_lit2var(lit);
  if (var >= types.size()) {
    types.resize(var + 1);  // default-constructed AigerType values.
  }
  if (var > maxvar) maxvar = var;
}

// Checks whether the literal 'lit' is already defined.
// Returns an empty string if not defined; otherwise an error message.
std::string Aiger::alreadyDefined(unsigned lit, const AigerReader & reader) const
{
  assert(lit != 0);
  assert(!aiger_sign(lit));
  unsigned var = aiger_lit2var(lit);
  if (maxvar < var) return "";
  const AigerType & type = types[var];
  if (type.input)
    return "line " + std::to_string(reader.linenoAtLastTokenStart)
           + ": literal " + std::to_string(lit) + " already defined as input";
  if (type.latch)
    return "line " + std::to_string(reader.linenoAtLastTokenStart)
           + ": literal " + std::to_string(lit) + " already defined as latch";
  if (type.isAnd)
    return "line " + std::to_string(reader.linenoAtLastTokenStart)
           + ": literal " + std::to_string(lit) + " already defined as AND";
  return "";
}

// Reads the AIGER header (including symbol counts and symbol table entries)
// from the input via 'reader'. Returns an empty string on success, or an
// error message on failure.
std::string Aiger::readHeader(AigerReader & reader)
{
  std::string error;
  char delim = 0;

  // Read signature: expect 'a'
  reader.nextCh();
  if (reader.ch != 'a')
    return aiger_error_u("line %u: expected 'a' as first character",
                         reader.lineno);

  // Next, expect either 'i' or 'a'
  int c = reader.nextCh();
  if (c != 'i' && reader.ch != 'a')
    return aiger_error_u("line %u: expected 'i' or 'a' after 'a'",
                         reader.lineno);

  if (reader.ch == 'a')
    reader.mode = Mode::Ascii;
  else
    reader.mode = Mode::Binary;

  if (reader.nextCh() != 'g')
    return aiger_error_u("line %u: expected 'g' after 'a[ai]'",
                         reader.lineno);

  if (reader.nextCh() != ' ')
    return aiger_error_u("line %u: expected ' ' after 'a[ai]g'",
                         reader.lineno);

  reader.nextCh();  // skip the space

  // Read header numbers:
  error = reader.readLiteral("maximum variable index", reader.maxvar, ' ');
  if (!error.empty()) return error;

  error = reader.readLiteral("number of inputs", reader.inputs, ' ');
  if (!error.empty()) return error;

  error = reader.readLiteral("number of latches", reader.latches, ' ');
  if (!error.empty()) return error;

  error = reader.readLiteral("number of outputs", reader.outputs, ' ');
  if (!error.empty()) return error;

  error = reader.readLiteral("number of and gates", reader.ands, 0, &delim);
  if (!error.empty()) return error;

  if (delim == ' ') {
    error = reader.readLiteral(
        "number of bad state constraints", reader.bad, 0, &delim);
    if (!error.empty()) return error;
  }
  if (delim == ' ') {
    error = reader.readLiteral(
        "number of invariant constraints", reader.constraints, 0, &delim);
    if (!error.empty()) return error;
  }
  if (delim == ' ') {
    error = reader.readLiteral(
        "number of justice constraints", reader.justice, 0, &delim);
    if (!error.empty()) return error;
  }
  if (delim == ' ') {
    error = reader.readLiteral(
        "number of fairness constraints", reader.fairness, '\n', nullptr);
    if (!error.empty()) return error;
  }

  // In binary mode, check consistency.
  if (reader.mode == Mode::Binary) {
    unsigned total = reader.inputs + reader.latches + reader.ands;
    if (total != reader.maxvar)
      return aiger_error_u("line %u: invalid maximal variable index",
                           reader.lineno);
  }

  // Set the circuit's maxvar.
  maxvar = reader.maxvar;

  // Resize internal vectors using our fitVector helper.
  types.resize(maxvar + 1);
  inputs.reserve(reader.inputs);
  latches.reserve(reader.latches);
  outputs.reserve(reader.outputs);
  ands.reserve(reader.ands);
  bad.reserve(reader.bad);
  constraints.reserve(reader.constraints);
  justice.reserve(reader.justice);
  fairness.reserve(reader.fairness);

  // Read input symbols.
  for (unsigned i = 0; i < reader.inputs; i++) {
    unsigned lit = 0;
    if (reader.mode == Mode::Ascii) {
      error = reader.readLiteral("input literal", lit, '\n');
      if (!error.empty()) return error;
      if (!lit || aiger_sign(lit) || aiger_lit2var(lit) > maxvar)
        return aiger_error_uu("line %u: literal %u is not a valid input",
                              reader.linenoAtLastTokenStart,
                              lit);
      error = alreadyDefined(lit, reader);
      if (!error.empty()) return error;
    } else {
      lit = 2 * (i + 1);
    }
    addInput(lit, "");
  }

  // Read latch symbols.
  for (unsigned i = 0; i < reader.latches; i++) {
    unsigned lit = 0;
    if (reader.mode == Mode::Ascii) {
      error = reader.readLiteral("latch literal", lit, ' ');
      if (!error.empty()) return error;
      if (!lit || aiger_sign(lit) || aiger_lit2var(lit) > maxvar)
        return aiger_error_uu("line %u: literal %u is not a valid latch",
                              reader.linenoAtLastTokenStart,
                              lit);
      error = alreadyDefined(lit, reader);
      if (!error.empty()) return error;
    } else {
      lit = 2 * (i + reader.inputs + 1);
    }
    unsigned next = 0;
    error = reader.readLiteral("next state literal", next, 0, &delim);
    if (!error.empty()) return error;
    if (aiger_lit2var(next) > maxvar)
      return aiger_error_uu("line %u: literal %u is not a valid literal",
                            reader.linenoAtLastTokenStart,
                            next);
    addLatch(lit, next, "");
    if (delim == ' ') {
      unsigned reset = 0;
      error = reader.readLiteral("reset literal", reset, '\n', nullptr);
      if (!error.empty()) return error;
      addReset(lit, reset);
    }
  }

  // Read output symbols.
  for (unsigned i = 0; i < reader.outputs; i++) {
    unsigned lit = 0;
    error = reader.readLiteral("output literal", lit, '\n', nullptr);
    if (!error.empty()) return error;
    if (aiger_lit2var(lit) > maxvar)
      return aiger_error_uu("line %u: literal %u is not a valid output",
                            reader.linenoAtLastTokenStart,
                            lit);
    addOutput(lit, "");
  }

  // Read bad state constraint symbols.
  for (unsigned i = 0; i < reader.bad; i++) {
    unsigned lit = 0;
    error = reader.readLiteral(
        "bad state constraint literal", lit, '\n', nullptr);
    if (!error.empty()) return error;
    if (aiger_lit2var(lit) > maxvar)
      return aiger_error_uu("line %u: literal %u is not valid bad",
                            reader.linenoAtLastTokenStart,
                            lit);
    addBad(lit, "");
  }

  // Read invariant constraint symbols.
  for (unsigned i = 0; i < reader.constraints; i++) {
    unsigned lit = 0;
    error = reader.readLiteral(
        "invariant constraint literal", lit, '\n', nullptr);
    if (!error.empty()) return error;
    if (aiger_lit2var(lit) > maxvar)
      return aiger_error_uu("line %u: literal %u is not a valid constraint",
                            reader.linenoAtLastTokenStart,
                            lit);
    addConstraint(lit, "");
  }

  // Read justice constraint symbols.
  if (reader.justice > 0) {
    std::vector<unsigned> sizes(reader.justice);
    for (unsigned i = 0; i < reader.justice; i++) {
      error = reader.readLiteral(
          "justice constraint size", sizes[i], '\n', nullptr);
      if (!error.empty()) return error;
    }
    for (unsigned i = 0; i < reader.justice; i++) {
      std::vector<unsigned> lits(sizes[i]);
      for (unsigned j = 0; j < sizes[i]; j++) {
        error = reader.readLiteral(
            "justice constraint literal", lits[j], '\n', nullptr);
        if (!error.empty()) return error;
      }
      addJustice(sizes[i], lits.data(), "");
    }
  }

  // Read fairness constraint symbols.
  for (unsigned i = 0; i < reader.fairness; i++) {
    unsigned lit = 0;
    error =
        reader.readLiteral("fairness constraint literal", lit, '\n', nullptr);
    if (!error.empty()) return error;
    if (aiger_lit2var(lit) > maxvar)
      return aiger_error_uu("line %u: literal %u is not valid fairness",
                            reader.linenoAtLastTokenStart,
                            lit);
    addFairness(lit, "");
  }

  reader.doneWithHeader = true;
  reader.looksLikeAAG = true;

  return "";
}  // end of readHeader
// Reads the ASCII portion for AND gates from the input via reader.
// Returns an empty string on success or an error message otherwise.
std::string Aiger::readAscii(AigerReader & reader)
{
  std::string error;
  unsigned lhs = 0, rhs0 = 0, rhs1 = 0;
  // Process each AND gate entry.
  for (unsigned i = 0; i < reader.ands; i++) {
    // Read the left-hand side literal for the AND gate.
    error = reader.readLiteral("and gate left-hand side literal", lhs, ' ');
    if (!error.empty()) return error;

    // Validate the LHS literal.
    if (!lhs || aiger_sign(lhs) || aiger_lit2var(lhs) > maxvar)
      return aiger_error_uu("line %u: literal %u is not a valid LHS of AND",
                            reader.linenoAtLastTokenStart,
                            lhs);

    // Check if this literal has already been defined.
    error = alreadyDefined(lhs, reader);
    if (!error.empty()) return error;

    // Read the first right-hand side literal.
    error = reader.readLiteral(
        "and gate first right-hand side literal", rhs0, ' ');
    if (!error.empty()) return error;

    if (aiger_lit2var(rhs0) > maxvar)
      return aiger_error_uu("line %u: literal %u is not a valid literal",
                            reader.linenoAtLastTokenStart,
                            rhs0);

    // Read the second right-hand side literal.
    error = reader.readLiteral(
        "and gate first right-hand side literal", rhs1, '\n');
    if (!error.empty()) return error;

    if (aiger_lit2var(rhs1) > maxvar)
      return aiger_error_uu("line %u: literal %u is not a valid literal",
                            reader.linenoAtLastTokenStart,
                            rhs1);

    // Register the AND gate in the circuit.
    addAnd(lhs, rhs0, rhs1);
  }
  return "";
}  // end of readAscii

// Reads the binary-encoded AND gates from the reader.
// Returns an empty string on success, or an error message.
std::string Aiger::readBinary(AigerReader & reader)
{
  unsigned lhs = maxInputOrLatch();  // returns the maximum literal among
                                     // inputs and latches.
  unsigned delta = 0;
  for (unsigned i = 0; i < reader.ands; i++) {
    lhs += 2;
    unsigned currentCharNo = reader.charno;
    std::string error = reader.readDelta(delta);
    if (!error.empty()) return error;
    if (delta > lhs)
      return aiger_error_u("character %u: invalid delta", currentCharNo);

    unsigned rhs0 = lhs - delta;
    currentCharNo = reader.charno;
    error = reader.readDelta(delta);
    if (!error.empty()) return error;
    if (delta > rhs0)
      return aiger_error_u("character %u: invalid delta", currentCharNo);

    unsigned rhs1 = rhs0 - delta;
    addAnd(lhs, rhs0, rhs1);
  }
  return "";
}

// Reads comment lines from the reader.
// Assumes that the current character (reader.ch) is '\n'.
// Returns an empty string on success or an error message.
std::string Aiger::readComments(AigerReader & reader)
{
  // Precondition: the current character is '\n'
  if (reader.ch != '\n')
    return aiger_error_u("line %u: expected newline at start of comment",
                         reader.lineno);

  reader.nextCh();  // consume the newline

  // Continue reading until end-of-file.
  while (reader.ch != EOF) {
    // Read a single comment line.
    while (reader.ch != '\n') {
      reader.pushChar(static_cast<char>(reader.ch));
      reader.nextCh();
      if (reader.ch == EOF)
        return aiger_error_u("line %u: new line after comment missing",
                             reader.lineno);
    }
    reader.nextCh();  // consume the newline

    // Now add the accumulated comment line to the circuit.
    addComment(reader.buffer);
    // Clear the buffer for the next comment.
    reader.buffer.clear();
  }
  return "";
}

// Reads the symbol table and comment section from the input stream (via
// reader) and populates the circuit's symbol vectors. Returns an empty string
// on success; otherwise, an error message.
std::string Aiger::readSymbolsAndComments(AigerReader & reader)
{
  // Ensure the reader's buffer is empty.
  reader.buffer.clear();

  // Loop until EOF.
  for (unsigned count = 0;; count++) {
    // If we reached EOF, we're done.
    if (reader.ch == EOF) return "";

    // Check that the current character is one of the valid symbol type
    // letters.
    char typeChar = static_cast<char>(reader.ch);
    if (typeChar != 'i' && typeChar != 'l' && typeChar != 'o'
        && typeChar != 'b' && typeChar != 'c' && typeChar != 'j'
        && typeChar != 'f') {
      if (reader.looksLikeAAG)
        return aiger_error_u(
            "line %u: corrupted symbol table ('aig' instead of 'aag' "
            "header?)",
            reader.lineno);
      return aiger_error_u("line %u: expected '[cilobcjf]' or EOF",
                           reader.lineno);
    }

    const char * typeName = nullptr;
    const char * typePos = nullptr;
    unsigned num = 0;
    std::vector<AigerSymbol> * symbols = nullptr;

    // Special case: 'c' can start either a comment or a constraint symbol.
    if (typeChar == 'c') {
      reader.nextCh();  // consume the 'c'
      if (reader.ch == '\n')
        return readComments(
            reader);  // readComments() is another member function.
      typeName = "constraint";
      typePos = "constraint";
      num = constraints.size();  // e.g., returns constraints.size()
      symbols = &constraints;
      if (num == 0)
        return aiger_error_u(
            "line %u: unexpected invariance constraint symbol entry prefix "
            "'c ' (comment sections start with 'c<new-line>' without space)",
            reader.linenoAtLastTokenStart);
    } else {
      // For other symbol types, choose based on the typeChar.
      switch (typeChar) {
        case 'i':
          typeName = "input";
          typePos = "input";
          num = inputs.size();
          symbols = &inputs;
          break;
        case 'l':
          typeName = "latch";
          typePos = "latch";
          num = latches.size();
          symbols = &latches;
          break;
        case 'o':
          typeName = "output";
          typePos = "output";
          num = outputs.size();
          symbols = &outputs;
          break;
        case 'b':
          typeName = "bad";
          typePos = "bad";
          num = bad.size();
          symbols = &bad;
          break;
        case 'j':
          typeName = "justice";
          typePos = "justice";
          num = justice.size();
          symbols = &justice;
          break;
        case 'f':
          typeName = "fairness";
          typePos = "fairness";
          num = fairness.size();
          symbols = &fairness;
          break;
        default:
          return aiger_error_u("line %u: unknown symbol type", reader.lineno);
      }
      reader.nextCh();  // consume the type character.
    }

    // Read the entry position for the symbol.
    unsigned pos = 0;
    std::string error = reader.readLiteral(typePos, pos, ' ');
    if (!error.empty()) return error;

    if (pos >= num)
      return aiger_error_usu(
          "line %u: %s symbol table entry position %u too large",
          reader.linenoAtLastTokenStart,
          typeName,
          pos);

    // Get the symbol at the specified position.
    AigerSymbol & sym = (*symbols)[pos];

    if (!sym.name.empty())
      return aiger_error_usu("line %u: %s literal %u has multiple symbols",
                             reader.linenoAtLastTokenStart,
                             typeName,
                             sym.lit);

    // Read the symbol name: append characters until a newline or EOF.
    while (reader.ch != '\n' && reader.ch != EOF) {
      reader.pushChar(static_cast<char>(reader.ch));
      reader.nextCh();
    }
    if (reader.ch == EOF)
      return aiger_error_u("line %u: new line missing", reader.lineno);
    // Expect a newline.
    assert(reader.ch == '\n');
    reader.nextCh();  // consume the newline

    // Append a null terminator to the buffer (optional with std::string).
    reader.pushChar('\0');
    // In C the name is copied; here we can simply assign.
    sym.name = reader.buffer;

    // Clear the buffer for the next symbol.
    reader.buffer.clear();
  }
  // (This point is never reached.)
  return "";
}  // end of readSymbolsAndComments

/// Reads the entire circuit from an input stream.
/// Returns an empty string on success or an error message on failure.
std::string Aiger::readFromStream(std::istream & in)
{
  // Construct a reader from the stream.
  AigerReader reader(in);
  // Initialize reader state.
  reader.lineno = 1;
  reader.buffer.clear();
  reader.ch = ' ';  // Initial dummy value.

  // Read header.
  std::string error = readHeader(reader);
  if (!error.empty()) return error;

  // Read the main body (either ASCII or binary).
  if (reader.mode == Mode::Ascii)
    error = readAscii(reader);
  else
    error = readBinary(reader);
  if (!error.empty()) return error;

  // Read symbol table and comments.
  error = readSymbolsAndComments(reader);
  if (!error.empty()) return error;

  // No need to delete the buffer; std::string manages its memory.

  // Perform a final consistency check.
  return check();  // Returns "" if no error.
}

/// Reads the circuit from a file (by filename).
/// Returns an empty string on success or an error message on failure.
std::string Aiger::readFromFile(const std::string & fileName)
{
  std::ifstream in(fileName, std::ios::binary);
  if (!in) return "Failed to open file: " + fileName;
  return readFromStream(in);
}

// Writes a single character to out.
int Aiger::defaultPut(std::ostream & out, char ch) const
{
  out.put(ch);
  return (out.fail() ? EOF : 0);
}

// Writes a string to out.
int Aiger::putS(std::ostream & out, const std::string & s) const
{
  out << s;
  return out.fail() ? EOF : static_cast<int>(s.size());
}

// Writes an unsigned integer as a string to out.
int Aiger::putU(std::ostream & out, unsigned u) const
{
  std::string s = std::to_string(u);
  return putS(out, s);
}

// Writes a delta-encoded unsigned number.
int Aiger::writeDelta(std::ostream & out, unsigned delta) const
{
  unsigned tmp = delta;
  unsigned char ch;
  while (tmp & ~0x7FU) {
    ch = static_cast<unsigned char>(tmp & 0x7F);
    ch |= 0x80;
    if (defaultPut(out, ch) == EOF) return 0;
    tmp >>= 7;
  }
  ch = static_cast<unsigned char>(tmp);
  return (defaultPut(out, ch) == EOF) ? 0 : 1;
}

// Writes the header line.
int Aiger::writeHeader(std::ostream & out,
                const std::string & formatString,
                bool compactInputsAndLatches) const
{
  if (putS(out, formatString) == EOF) return 0;
  if (defaultPut(out, ' ') == EOF) return 0;
  if (putU(out, maxvar) == EOF) return 0;
  if (defaultPut(out, ' ') == EOF) return 0;
  if (putU(out, inputs.size()) == EOF) return 0;
  if (defaultPut(out, ' ') == EOF) return 0;
  if (putU(out, latches.size()) == EOF) return 0;
  if (defaultPut(out, ' ') == EOF) return 0;
  if (putU(out, outputs.size()) == EOF) return 0;
  if (defaultPut(out, ' ') == EOF) return 0;
  if (putU(out, ands.size()) == EOF) return 0;

  if (!bad.empty() || !constraints.empty() || !justice.empty()
      || !fairness.empty()) {
    if (defaultPut(out, ' ') == EOF) return 0;
    if (putU(out, bad.size()) == EOF) return 0;
  }
  if (!constraints.empty() || !justice.empty() || !fairness.empty()) {
    if (defaultPut(out, ' ') == EOF) return 0;
    if (putU(out, constraints.size()) == EOF) return 0;
  }
  if (!justice.empty() || !fairness.empty()) {
    if (defaultPut(out, ' ') == EOF) return 0;
    if (putU(out, justice.size()) == EOF) return 0;
  }
  if (!fairness.empty()) {
    if (defaultPut(out, ' ') == EOF) return 0;
    if (putU(out, fairness.size()) == EOF) return 0;
  }
  if (defaultPut(out, '\n') == EOF) return 0;

  if (!compactInputsAndLatches && !inputs.empty()) {
    for (size_t i = 0; i < inputs.size(); i++) {
      if (putU(out, inputs[i].lit) == EOF || defaultPut(out, '\n') == EOF)
        return 0;
    }
  }

  if (!latches.empty()) {
    for (size_t i = 0; i < latches.size(); i++) {
      if (!compactInputsAndLatches) {
        if (putU(out, latches[i].lit) == EOF || defaultPut(out, ' ') == EOF)
          return 0;
      }
      if (putU(out, latches[i].next) == EOF) return 0;
      if (latches[i].reset) {
        if (defaultPut(out, ' ') == EOF) return 0;
        if (putU(out, latches[i].reset) == EOF) return 0;
      }
      if (defaultPut(out, '\n') == EOF) return 0;
    }
  }

  if (!outputs.empty()) {
    for (size_t i = 0; i < outputs.size(); i++) {
      if (putU(out, outputs[i].lit) == EOF || defaultPut(out, '\n') == EOF)
        return 0;
    }
  }

  if (!bad.empty()) {
    for (size_t i = 0; i < bad.size(); i++) {
      if (putU(out, bad[i].lit) == EOF || defaultPut(out, '\n') == EOF)
        return 0;
    }
  }

  if (!constraints.empty()) {
    for (size_t i = 0; i < constraints.size(); i++) {
      if (putU(out, constraints[i].lit) == EOF
          || defaultPut(out, '\n') == EOF)
        return 0;
    }
  }

  if (!justice.empty()) {
    for (size_t i = 0; i < justice.size(); i++) {
      if (putU(out, justice[i].lits.size()) == EOF
          || defaultPut(out, '\n') == EOF)
        return 0;
    }
    for (size_t i = 0; i < justice.size(); i++) {
      for (size_t j = 0; j < justice[i].lits.size(); j++) {
        if (putU(out, justice[i].lits[j]) == EOF
            || defaultPut(out, '\n') == EOF)
          return 0;
      }
    }
  }

  if (!fairness.empty()) {
    for (size_t i = 0; i < fairness.size(); i++) {
      if (putU(out, fairness[i].lit) == EOF || defaultPut(out, '\n') == EOF)
        return 0;
    }
  }
  return 1;
}

// --- Symbol Table Helpers ---

bool Aiger::haveAtLeastOneSymbolAux(const std::vector<AigerSymbol> & symbols) const
{
  for (const auto & sym : symbols)
    if (!sym.name.empty()) return true;
  return false;
}

bool Aiger::haveAtLeastOneSymbol() const
{
  return haveAtLeastOneSymbolAux(inputs) || haveAtLeastOneSymbolAux(outputs)
         || haveAtLeastOneSymbolAux(latches) || haveAtLeastOneSymbolAux(bad)
         || haveAtLeastOneSymbolAux(constraints)
         || haveAtLeastOneSymbolAux(justice)
         || haveAtLeastOneSymbolAux(fairness);
}

int Aiger::writeSymbolsAux(std::ostream & out,
                    const std::string & typeLabel,
                    const std::vector<AigerSymbol> & symbols) const
{
  for (size_t i = 0; i < symbols.size(); i++) {
    if (symbols[i].name.empty()) continue;
    // Write type label, position, and the symbol name.
    if (putS(out, typeLabel) == EOF || defaultPut(out, ' ') == EOF
        || putU(out, i) == EOF || defaultPut(out, ' ') == EOF
        || putS(out, symbols[i].name) == EOF || defaultPut(out, '\n') == EOF)
      return 0;
  }
  return 1;
}

int Aiger::writeSymbols(std::ostream & out) const
{
  if (!writeSymbolsAux(out, "i", inputs)) return 0;
  if (!writeSymbolsAux(out, "l", latches)) return 0;
  if (!writeSymbolsAux(out, "o", outputs)) return 0;
  if (!writeSymbolsAux(out, "b", bad)) return 0;
  if (!writeSymbolsAux(out, "c", constraints)) return 0;
  if (!writeSymbolsAux(out, "j", justice)) return 0;
  if (!writeSymbolsAux(out, "f", fairness)) return 0;
  return 1;
}

// Writes symbols to stream.
bool Aiger::writeSymbolsToStream(std::ostream & out) const
{
  return writeSymbols(out) != 0;
}

// --- Comments ---

int Aiger::writeComments(std::ostream & out) const
{
  for (const auto & com : comments) {
    if (putS(out, com) == EOF) return 0;
    if (defaultPut(out, '\n') == EOF) return 0;
  }
  return 1;
}

bool Aiger::writeCommentsToStream(std::ostream & out) const
{
  return writeComments(out) != 0;
}

// --- ASCII and Binary Output ---

int Aiger::writeAscii(std::ostream & out)
{
  // Ensure the circuit is consistent.
  if (!check().empty()) return 0;
  if (writeHeader(out, "aag", false) == 0) return 0;
  for (const auto & gate : ands) {
    if (putU(out, gate.lhs) == EOF || defaultPut(out, ' ') == EOF
        || putU(out, gate.rhs0) == EOF || defaultPut(out, ' ') == EOF
        || putU(out, gate.rhs1) == EOF || defaultPut(out, '\n') == EOF)
      return 0;
  }
  return 1;
}

int Aiger::writeBinary(std::ostream & out)
{
  if (!check().empty()) return 0;
  reencode();  // perform reencoding
  if (writeHeader(out, "aig", true) == 0) return 0;
  unsigned lhs = maxInputOrLatch() + 2;
  for (const auto & gate : ands) {
    assert(lhs == gate.lhs);
    assert(lhs > gate.rhs0);
    assert(gate.rhs0 >= gate.rhs1);
    if (!writeDelta(out, lhs - gate.rhs0)) return 0;
    if (!writeDelta(out, gate.rhs0 - gate.rhs1)) return 0;
    lhs += 2;
  }
  return 1;
}

// --- Strip Symbols and Comments ---

// Dummy implementations of deleteSymbols and deleteComments.
unsigned Aiger::deleteSymbols(std::vector<AigerSymbol> & symbols)
{
  unsigned count = 0;
  for (auto & sym : symbols) {
    if (!sym.name.empty()) {
      count++;
      sym.name.clear();
    }
  }
  return count;
}
unsigned Aiger::deleteComments()
{
  unsigned count = comments.size();
  comments.clear();
  return count;
}

// (Assume deleteSymbols() and deleteComments() clear the corresponding
// vectors and return the count of removed items.)
unsigned Aiger::stripSymbolsAndComments()
{
  unsigned res = deleteComments();
  res += deleteSymbols(inputs);
  res += deleteSymbols(latches);
  res += deleteSymbols(outputs);
  res += deleteSymbols(bad);
  res += deleteSymbols(constraints);
  res += deleteSymbols(justice);
  res += deleteSymbols(fairness);
  return res;
}

// --- Generic Write ---

// Writes the entire circuit to stream in the specified mode.
// Returns true on success, false on failure.
bool Aiger::writeGeneric(Mode mode, std::ostream & out)
{
  if (!check().empty()) return false;
  if (mode == Mode::Ascii) {
    if (writeAscii(out) == 0) return false;
  } else {
    if (writeBinary(out) == 0) return false;
  }
  if (mode != Mode::Stripped) {
    if (haveAtLeastOneSymbol()) {
      if (writeSymbols(out) == 0) return false;
    }
    if (!comments.empty()) {
      if (putS(out, "c\n") == EOF) return false;
      if (writeComments(out) == 0) return false;
    }
  }
  return true;
}

// Writes the circuit to a stream.
bool Aiger::writeToStream(Mode mode, std::ostream & out)
{
  return writeGeneric(mode, out);
}

// Writes the circuit to a file.
bool Aiger::writeToFile(Mode mode, const std::string & filename)
{
  std::ofstream ofs(filename, std::ios::binary);
  if (!ofs) return false;
  bool res = writeGeneric(mode, ofs);
  ofs.close();
  return res;
}

// Writes the circuit to a string.
std::string Aiger::writeToString(Mode mode)
{
  std::ostringstream oss;
  if (!writeGeneric(mode, oss)) return "";
  return oss.str();
}


} // namespace aiger

