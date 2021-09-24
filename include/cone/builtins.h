       
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

  struct cone_exception : public std::exception {
     std::string s;
     explicit cone_exception(std::string ss) : s(ss) {}
     ~cone_exception() throw () {}
     const char* what() const throw() { return s.c_str(); }
  };

  typedef std::experimental::any object;

  typedef std::function<object(const object &)> cont;

  typedef std::shared_ptr<std::vector<std::map<std::string, object>>> states;

  typedef std::shared_ptr<std::vector<std::map<std::string, object>>> effects;

  typedef std::function<object(const cont &, states, effects)> funcWithCont;

  states ____make_empty_state() {
    auto s = std::make_shared<std::vector<std::map<std::string, object>>>();
    s->push_back({});
    return s;
  }

  effects ____make_empty_effs() {
    return std::make_shared<std::vector<std::map<std::string, object>>>();
  }

  inline py::object ____to_py_object(const object &o) {
    if (o.type() != typeid(py::object)) {
      throw cone_exception("cannot cast to py object, are you trying to capture continuation in while?");
    }
    return std::experimental::any_cast<py::object>(o);
  }

  namespace core { namespace prelude {
  const std::function<object(const cont &, states, effects, const object &)> cone__print = 
    [=](const cont &k, states s, effects effs, const object &a) -> object {
      py::print(std::experimental::any_cast<py::object>(a));
      return k(a);
    };
  }}

  inline bool ____is_none(const object &o) {
    return o.type() == typeid(py::object) && std::experimental::any_cast<py::object>(o).is(py::none());
  }

  inline object ____lookup_var(states s, const std::string &key) {
    for (auto it=s->rbegin(); it != s->rend(); ++it) {
      if (it->find(key) != it->end()) {
        return (*it)[key];
      }
    }
    return py::object(py::none());
  }

  inline object ____lookup_eff(effects effs, const std::string &key) {
    for (auto it=effs->rbegin(); it != effs->rend(); ++it) {
      if (it->find(key) != it->end()) {
        return (*it)[key];
      }
    }
    return py::object(py::none());
  }

  inline object ____add_var(states s, const std::string &key, const object &k) {
    s->back()[key] = k;
    return py::object(py::none());
  }

  inline object ____update_state(states s, const std::string &key, const object &k) {
    for (auto it=s->rbegin(); it != s->rend(); ++it) {
      if (it->find(key) != it->end()) {
        (*it)[key] = k;
        return py::object(py::none());
      }
    }
    throw cone_exception("cannot find variable " + key);
    return py::object(py::none());
  }

  inline object ____call_cps_with_cleared_vars(
    const cont &k, states s, effects es,
    const std::vector<std::string> &ks, const object &e) {
    states state = ____make_empty_state();
    *state = *s; 
    effects effs = ____make_empty_effs();
    for (auto it=state->rbegin(); it!=state->rend(); ++it) {
      for (auto k : ks) {
        it->erase(k);
      }
    }
    return std::experimental::any_cast<funcWithCont>(e)(k, state, effs);
  }

  struct ____deferred {
    explicit ____deferred(const object &v) : value(v) {}
    object value;
  };

  inline object ____while(const cont &k, states state, effects effs,
                          const object &cond0,
                          const object &body0) {
    state->push_back({});
    auto cond = std::experimental::any_cast<funcWithCont>(cond0);
    auto body = std::experimental::any_cast<funcWithCont>(body0);
    cont k2 = [=](const object &o) -> object {
      cont trampoline = [=](const object &o) -> object {
         if (py::cast<bool>(std::experimental::any_cast<py::object>(o))) {
           state->push_back({});
           return body([=](const object &o) -> object {
                        state->pop_back();
                        return cond([](const object &o) -> object{ 
                               return object(____deferred(o)); 
                             },
                            state, effs);}
                , state, effs);
         } else {
           state->pop_back();
           return k(o);
         }
      };
      auto d = trampoline(o);
      for (; d.type() == typeid(____deferred); 
           d = trampoline(std::experimental::any_cast<____deferred>(d).value));
      return d;
    };
    return cond(k2, state, effs);
  }

  inline object ____case(const cont &k, states state, effects effs, const object &ce,
                         const std::vector<cont> &conds,
                         const std::vector<object> &exprs) {
    for (unsigned i=0; i<conds.size(); ++i) {
      const auto &p = conds[i];
      const auto &e = std::experimental::any_cast<funcWithCont>(exprs[i]);
      state->push_back({});
      cont k2 = [state, k](const object &o) {
        state->pop_back();
        return k(o);
      };
      if (py::cast<bool>(std::experimental::any_cast<py::object>(p(ce)))) {
        return e(k2, state, effs);
      } else {
        state->pop_back();
      }
    }
    throw cone_exception("no matched case");
    return py::object(py::none());
  }

  const cont ____identity_k = [](const object &x) { return x; };

  inline object ____handle(const cont &k, states state, effects effs,
                           const object &scope, const std::map<std::string, object> &handlers) {
    state->push_back({});
    effs->push_back({});
    for (auto &p : handlers) {
      effs->back()[p.first] = p.second;
    }
    auto &&o = std::experimental::any_cast<funcWithCont>(scope)(____identity_k, state, effs);
    state->pop_back();
    effs->pop_back();
    return k(o);
  }

  constexpr auto ____resumed_k = "____resumed_k";

  inline object ____call_with_resumed_k(const cont &k, states state, effects effs, const object &handler) {
    state->push_back({});
    state->back()[____resumed_k] = k;
    auto h = std::experimental::any_cast<funcWithCont>(handler);
    return h([state](const object &x) { state->pop_back(); return x;}, state, effs);
  }

  const std::function<object(const cont &, states, effects, const object &)> cone__resume = 
    [=](const cont &k, states s, effects effs, const object &a) -> object {
      return k(std::experimental::any_cast<cont>(s->back()[____resumed_k])(a));
    };

}