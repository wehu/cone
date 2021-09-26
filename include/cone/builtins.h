#pragma once

#include <experimental/any>
#include <pybind11/pybind11.h>
#include <pybind11/functional.h>
#include <pybind11/eval.h>
#include <map>
#include <vector>
#include <iostream>

namespace cone {

  namespace py = pybind11;

  struct ____cone_exception : public std::exception {
     std::string s;
     explicit ____cone_exception(std::string ss) : s(ss) {}
     virtual ~____cone_exception() throw () {}
     const char* what() const throw() { return s.c_str(); }
  };

  typedef std::experimental::any object;

  typedef std::function<object(const object &)> cont_t;

  typedef std::shared_ptr<std::vector<std::map<std::string, object>>> stack_t;

  typedef std::shared_ptr<std::vector<std::map<std::string, object>>> effects_t;

  typedef std::function<object(const cont_t &, stack_t, effects_t)> func_with_cont_t;

  stack_t ____make_empty_stack() {
    auto s = std::make_shared<std::vector<std::map<std::string, object>>>();
    s->push_back({});
    return s;
  }

  effects_t ____make_empty_effs() {
    return std::make_shared<std::vector<std::map<std::string, object>>>();
  }

  inline py::object ____to_py_object(const object &o) {
    if (o.type() != typeid(py::object)) {
      throw ____cone_exception(std::string("cannot cast to py object, expected py object, but got ") + o.type().name());
    }
    return std::experimental::any_cast<py::object>(o);
  }

  namespace core { namespace prelude {
  const std::function<object(const cont_t &, stack_t, effects_t, const object &)> cone__print = 
    [=](const cont_t &k, stack_t s, effects_t effs, const object &a) -> object {
      py::print(std::experimental::any_cast<py::object>(a));
      return k(a);
    };
  }}

  inline bool ____is_none(const object &o) {
    return o.type() == typeid(py::object) && std::experimental::any_cast<py::object>(o).is(py::none());
  }

  inline object ____lookup_var(stack_t s, const std::string &key) {
    for (auto it=s->rbegin(); it != s->rend(); ++it) {
      if (it->find(key) != it->end()) {
        return (*it)[key];
      }
    }
    return py::object(py::none());
  }

  inline object ____lookup_eff(effects_t effs, const std::string &key) {
    for (auto it=effs->rbegin(); it != effs->rend(); ++it) {
      if (it->find(key) != it->end()) {
        return (*it)[key];
      }
    }
    return py::object(py::none());
  }

  inline object ____add_var(stack_t s, const std::string &key, const object &k) {
    s->back()[key] = k;
    return py::object(py::none());
  }

  inline object ____update_stack(stack_t s, const std::string &key, const object &k) {
    for (auto it=s->rbegin(); it != s->rend(); ++it) {
      if (it->find(key) != it->end()) {
        (*it)[key] = k;
        return py::object(py::none());
      }
    }
    throw ____cone_exception("cannot find variable " + key);
    return py::object(py::none());
  }

  inline object ____call_cps_with_cleared_vars(
    const cont_t &k, stack_t s, effects_t es,
    const std::vector<std::string> &ks, const object &e) {
    stack_t stack = ____make_empty_stack();
    *stack = *s; 
    effects_t effs = ____make_empty_effs();
    for (auto it=stack->rbegin(); it!=stack->rend(); ++it) {
      for (auto k : ks) {
        it->erase(k);
      }
    }
    return std::experimental::any_cast<func_with_cont_t>(e)(k, stack, effs);
  }

  struct ____deferred {
    explicit ____deferred(const object &v) : value(v) {}
    object value;
  };

  inline object ____while(const cont_t &k, stack_t stack, effects_t effs,
                          const object &cond0,
                          const object &body0) {
    stack->push_back({});
    auto cond = std::experimental::any_cast<func_with_cont_t>(cond0);
    auto body = std::experimental::any_cast<func_with_cont_t>(body0);
    cont_t k2 = [=](const object &o) -> object {
      cont_t trampoline = [=](const object &o) -> object {
         if (py::cast<bool>(std::experimental::any_cast<py::object>(o))) {
           stack->push_back({});
           return body([=](const object &o) -> object {
                        stack->pop_back();
                        return cond([](const object &o) -> object { 
                               return object(____deferred(o));},
                               stack, effs);}
                , stack, effs);
         } else {
           stack->pop_back();
           return k(o);
         }
      };
      auto d = trampoline(o);
      for (; d.type() == typeid(____deferred); 
           d = trampoline(std::experimental::any_cast<____deferred>(d).value));
      return d;
    };
    return cond(k2, stack, effs);
  }

  inline object ____case(const cont_t &k, stack_t stack, effects_t effs, const object &ce,
                         const std::vector<cont_t> &conds,
                         const std::vector<object> &exprs) {
    for (unsigned i=0; i<conds.size(); ++i) {
      const auto &p = conds[i];
      const auto &e = std::experimental::any_cast<func_with_cont_t>(exprs[i]);
      stack->push_back({});
      cont_t k2 = [stack, k](const object &o) {
        stack->pop_back();
        return k(o);
      };
      if (py::cast<bool>(std::experimental::any_cast<py::object>(p(ce)))) {
        return e(k2, stack, effs);
      } else {
        stack->pop_back();
      }
    }
    throw ____cone_exception("no matched case");
    return py::object(py::none());
  }

  const cont_t ____identity_k = [](const object &x) { return x; };

  inline object ____handle(const cont_t &k, stack_t stack, effects_t effs,
                           const object &scope, const std::map<std::string, object> &handlers) {
    stack->push_back({});
    effs->push_back({});
    for (auto &p : handlers) {
      effs->back()[p.first] = p.second;
    }
    auto &&o = std::experimental::any_cast<func_with_cont_t>(scope)(____identity_k, stack, effs);
    stack->pop_back();
    effs->pop_back();
    return k(o);
  }

  constexpr auto ____resumed_k = "____resumed_k";

  inline object ____call_with_resumed_k(const cont_t &k, stack_t stack, effects_t effs, const object &handler) {
    stack->push_back({});
    stack->back()[____resumed_k] = k;
    auto h = std::experimental::any_cast<func_with_cont_t>(handler);
    return h([stack](const object &x) { stack->pop_back(); return x;}, stack, effs);
  }

  const std::function<object(const cont_t &, stack_t, effects_t, const object &)> cone__resume = 
    [=](const cont_t &k, stack_t s, effects_t effs, const object &a) -> object {
      return k(std::experimental::any_cast<cont_t>(s->back()[____resumed_k])(a));
    };

  constexpr auto ____typeargs = "____typeargs";

  inline object ____set_typeargs(stack_t stack, const object &typeargs) {
    stack->back()[____typeargs] = typeargs;
    return py::object(py::none());
  }


}