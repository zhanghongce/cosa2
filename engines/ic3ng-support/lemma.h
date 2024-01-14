#pragma once

#include "model.h"

namespace pono
{

  class ModelLemmaManager;
    
  struct LCexOrigin{ // the origin of a model (and therefore its lemma to block)
    public:
      enum CexType {MUST_BLOCK, MAY_BLOCK, ORIGIN_FROM_INIT, PROPERTY, CONSTRAINT} cex_type;
    private:
      unsigned step_to_fail; // only matters for MUST_BLOCK
    public:
      LCexOrigin(CexType type, unsigned step) : cex_type(type), step_to_fail(step){}

      bool inline is_must_block() const { return cex_type == MUST_BLOCK; }
      bool inline is_may_block() const { return cex_type == MAY_BLOCK; }
      bool inline is_the_property() const { return cex_type == PROPERTY; }
      unsigned inline dist_to_fail() const { return step_to_fail; }
      CexType inline get_type() const { return cex_type;} 

      static LCexOrigin MustBlock(unsigned i) { return LCexOrigin(MUST_BLOCK, i); }
      static LCexOrigin MayBlock() { return LCexOrigin(MAY_BLOCK, 0); }
      static LCexOrigin FromInit() { return LCexOrigin(ORIGIN_FROM_INIT, 0); }
      static LCexOrigin FromProperty() { return LCexOrigin(PROPERTY, 0); }
      static LCexOrigin FromConstraint() { return LCexOrigin(CONSTRAINT, 0); }
  };

    // the lemma on a frame
  class Lemma {
    public:
    
    Lemma(const smt::Term & expr, Model * cex, LCexOrigin origin);
    
    inline smt::Term  expr() const { return expr_; }
    inline Model *  cex() const { return cex_; }
    inline std::string to_string() const { return expr()->to_string(); }
    inline LCexOrigin origin() const { return origin_; }

    
    bool pushed;

    Lemma * direct_push(ModelLemmaManager & mfm);
    Lemma * copy(ModelLemmaManager & mfm);

    // bool subsume_by_frame(unsigned fidx, LemmaPDRInterface & pdr);

    static std::string origin_to_string(LCexOrigin o) ;
    std::string dump_expr() const;
    std::string dump_cex() const;

    protected:
    // the expression : for btor
    smt::Term expr_;
    // the cex it blocks
    Model*  cex_;
    // status tracking
    LCexOrigin origin_;
  }; // class Lemma


// class to manage the memory of memory and frames
// apdr shall inherit from this
class ModelLemmaManager {
  friend class Lemma;
public:
  ModelLemmaManager ();
  virtual ~ModelLemmaManager();
  
  ModelLemmaManager & operator=(const ModelLemmaManager &) = delete;
  ModelLemmaManager(const ModelLemmaManager &) = delete;
  
  virtual smt::SmtSolver & solver() = 0;

protected:
  Model * new_model();
  void register_new_model(Model *);
  Model * new_model(const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset);
  Model * new_model_replace_var(
    const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset,
    const std::unordered_map<smt::Term, smt::Term> & varmap );

  Lemma * new_lemma(
    const smt::Term & expr, Model * cex, LCexOrigin origin);
    
  std::vector<Lemma *> lemma_allocation_pool;
  std::vector<Model *> cube_allocation_pool;
};

} // namespace pono
