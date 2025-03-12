#pragma once

#include "model.h"

namespace pono
{

  class ModelLemmaManager;
    
  struct LCexOrigin{ // the origin of a model (and therefore its lemma to block)
    public:
      enum CexType {MUST_BLOCK, MAY_BLOCK, ORIGIN_FROM_INIT, PROPERTY, CONSTRAINT, SIDE_LOAD} cex_type;
    private:
      unsigned step_to_fail; // only matters for MUST_BLOCK
    public:
      LCexOrigin(CexType type, unsigned step) : cex_type(type), step_to_fail(step){}

      bool inline is_must_block() const { return cex_type == MUST_BLOCK; }
      bool inline is_may_block() const { return cex_type == MAY_BLOCK; }
      bool inline is_the_property() const { return cex_type == PROPERTY; }
      bool inline is_constraint() const { return cex_type == CONSTRAINT; }
      bool inline is_side_load() const { return cex_type == SIDE_LOAD; }
      unsigned inline dist_to_fail() const { return step_to_fail; }
      CexType inline get_type() const { return cex_type;} 
      LCexOrigin to_prior_frame() const { 
        if (is_must_block()) 
          return LCexOrigin(MUST_BLOCK, step_to_fail+1);
        return *this; }

      static LCexOrigin MustBlock(unsigned i) { return LCexOrigin(MUST_BLOCK, i); }
      static LCexOrigin MayBlock() { return LCexOrigin(MAY_BLOCK, 0); }
      static LCexOrigin FromInit() { return LCexOrigin(ORIGIN_FROM_INIT, 0); }
      static LCexOrigin FromProperty() { return LCexOrigin(PROPERTY, 0); }
      static LCexOrigin FromConstraint() { return LCexOrigin(CONSTRAINT, 0); }
      static LCexOrigin FromSideLoad() { return LCexOrigin(SIDE_LOAD, 0); }
  };

    // the lemma on a frame
  class Lemma {
    public:
    
    Lemma(const smt::Term & expr, smt::TermVec && cube, Model * cex, LCexOrigin origin) : 
      expr_(expr), cube_(std::move(cube)), 
      cex_(cex),  origin_(origin) { }
    
    inline smt::Term  expr() const { return expr_; }
    inline const smt::TermVec & cube() const { return cube_; }
    inline Model *  cex() const { return cex_; }
    inline std::string to_string() const { return expr()->to_string(); }
    inline LCexOrigin origin() const { return origin_; }

    // bool pushed;

    // Lemma * direct_push(ModelLemmaManager & mfm);
    // Lemma * copy(ModelLemmaManager & mfm);

    // bool subsume_by_frame(unsigned fidx, LemmaPDRInterface & pdr);

    // static std::string origin_to_string(LCexOrigin o) ;
    // std::string dump_expr() const;
    // std::string dump_cex() const;

    protected:
    // the expression : for btor
    // the expr should be not(Conj(var==val)) for var,val in cube
    smt::Term expr_;

    // cube_ is just a vector of var==val
    smt::TermVec cube_;

    // a map: term->term, var == val
    // cube_t cube_;

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
  // [deprecated]
  // Model * new_model();
  // void register_new_model(Model *);
  // by default, move in
  Model * new_model(smt::UnorderedTermSet && slicedvarset, 
                    smt::UnorderedTermSet && unslicedvarset,
                    smt::TermVec && eqs);
  // Model * new_model_replace_var(
  //   const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset,
  //   const std::unordered_map<smt::Term, smt::Term> & varmap );

  Lemma * new_lemma(
    const smt::Term & expr, Model * cex, LCexOrigin origin, smt::TermVec && cube = {});
    
  std::vector<Lemma *> lemma_allocation_pool;
  std::vector<Model *> cube_allocation_pool;
  std::unordered_map<std::string, PerSlicedVarInfo *> cube_slicedvar_info_allocation_pool;
  std::unordered_map<std::string, PerUnslicedVarInfo *> cube_unslicevar_info_allocation_pool;
};

} // namespace pono
