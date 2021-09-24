       
#pragma once

#include <pybind11/pybind11.h>
#include <pybind11/functional.h>
#include <pybind11/eval.h>
#include <map>
#include <iostream>

namespace cone {

  namespace py = pybind11;

  typedef py::object object;

  typedef object cont;

  typedef object states;

  typedef object effects;

  namespace core { namespace prelude {
  inline object cone__print(const cont &k, states s, effects effs, const object &a) {
    py::print(a);
    return k(a);
  }
  }}

  inline object ____lookup_var(states s, const std::string &key) {
    auto l = py::cast<py::list>(s);
    for (auto it=l.begin(); it != l.end(); ++it) {
      auto m = py::cast<py::dict>(*it);
      if (m.contains(key)) {
        return m[key.c_str()];
      }
    }
    return py::none();
  }

  inline object ____lookup_eff(effects effs, const std::string &key) {
    auto l = py::cast<py::list>(effs);
    for (auto it=l.begin(); it != l.end(); ++it) {
      auto m = py::cast<py::dict>(*it);
      if (m.contains(key)) {
        return m[key.c_str()];
      }
    }
    return py::none();
  }

  inline object ____add_var(states s, const std::string &key, const object &k) {
    auto l = py::cast<py::list>(s);
    auto m = py::cast<py::dict>(l[0]);
    m[key.c_str()] = k;
    return py::none();
  }

  inline object ____update_state(states s, const std::string &key, const object &k) {
    auto l = py::cast<py::list>(s);
    for (auto it=l.begin(); it != l.end(); ++it) {
      auto m = py::cast<py::dict>(*it);
      if (m.contains(key)) {
        m[key.c_str()] = k;
        return py::none();
      }
    }
    return py::none();
  }

  inline object ____call_cps_with_cleared_vars(
    const cont &k, states s, effects es,
    const std::vector<std::string> &ks, const object &e) {
    states state = py::module_::import("copy").attr("deepcopy")(s);
    effects effs = py::list();
    auto l = py::cast<py::list>(state);
    for (auto it=l.begin(); it!=l.end(); ++it) {
      auto m = py::cast<py::dict>(*it);
      for (auto k : ks) {
        if (m.contains(k)) {
          m.attr("pop")(k.c_str());
        }
      }
    }
    auto kk = py::cast<std::function<object(const object &)>>(k);
    auto ee = py::cast<std::function<object(const std::function<object(const object &)> &, states, effects)>>(e);
    return ee(kk, state, effs);
  }

  inline object ____while(const cont &k, states state, effects effs,
                          const object &cond0,
                          const object &body0) {
    auto l = py::cast<py::list>(state);
    l.insert(0, py::dict());
    auto cond = py::cast<std::function<object(const std::function<object(const object &)> &, states, effects)>>(cond0);
    auto body = py::cast<std::function<object(const std::function<object(const object &)> &, states, effects)>>(body0);
    std::function<object(const object &)> k2;
    std::shared_ptr<std::function<object(const object &)>> k3 = std::make_shared<std::function<object(const object &)>>();
    k2 = [state, effs, k, k3, body](const object &o) {
      auto l = py::cast<py::list>(state);
      if (py::cast<bool>(o)) {
        l.insert(0, py::dict());
        return body(*k3, state, effs);
      } else {
        l.attr("pop")(0);
        return k(o);
      }
    };
    *k3 = [state, effs, k2, cond](const object &o) {
      auto l = py::cast<py::list>(state);
      l.attr("pop")(0);
      return cond(k2, state, effs);
    };
    return cond(k2, state, effs);
  }

  inline object ____case(const cont &k, states state, effects effs, const object &ce,
                         const std::vector<object> &conds,
                         const std::vector<object> &exprs) {
    for (unsigned i=0; i<conds.size(); ++i) {
      const auto &p = py::cast<std::function<object(const object &)>>(conds[i]);
      const auto &e = py::cast<std::function<object(const std::function<object(const object &)> &, states, effects)>>(exprs[i]);
      auto l = py::cast<py::list>(state);
      l.insert(0, py::dict());
      std::function<object(const object &)> k2 = [state, k](const object &o) {
        auto l = py::cast<py::list>(state);
        l.attr("pop")(0);
        return k(o);
      };
      if (py::cast<bool>(p(ce))) {
        return e(k2, state, effs);
      } else {
        l.attr("pop")(0);
      }
    }
    return py::none();
  }

  const cont ____identity_k = py::cpp_function([](const object &x) { return x; });

  inline object ____handle(const cont &k, states state, effects effs,
                           const object &scope, const std::map<std::string, object> &handlers) {
    auto sl = py::cast<py::list>(state);
    auto el = py::cast<py::list>(effs);
    sl.insert(0, py::dict());
    el.insert(0, py::dict());
    auto m = py::cast<py::dict>(el[0]);
    for (auto &p : handlers) {
      m[p.first.c_str()] = p.second;
    }
    auto &&o = scope(____identity_k, state, effs);
    sl.attr("pop")(0);
    el.attr("pop")(0);
    return k(o);
  }

  constexpr auto ____resumed_k = "____resumed_k";

  inline object ____call_with_resumed_k(const cont &k, states state, effects effs, const object &handler) {
    auto l = py::cast<py::list>(state);
    l.insert(0, py::dict());
    auto m = py::cast<py::dict>(l[0]);
    m[____resumed_k] = k;
    auto h = py::cast<std::function<object(const std::function<object(const object &)> &, states, effects)>>(handler);
    return h([state](const object &x) { auto l = py::cast<py::list>(state); l.attr("pop")(0); return x;}, state, effs);
  }

  inline object cone__resume(const cont &k, states s, effects effs, const object &a) {
    auto l = py::cast<py::list>(s);
    auto m = py::cast<py::dict>(l[0]);
    return k(m[____resumed_k](a));
  }

}