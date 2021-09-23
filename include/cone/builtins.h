       
#pragma once

#include <pybind11/pybind11.h>
#include <pybind11/functional.h>
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
    return e(k, state, effs);
  }

  inline object ____while(const cont &k, states state, effects effs,
                          const object &cond,
                          const object &body) {
    auto l = py::cast<py::list>(state);
    l.insert(0, py::dict());
    cont k2;
    std::shared_ptr<cont> k3 = std::make_shared<cont>();
    k2 = py::cpp_function([state, effs, k, k3, body](const object &o) {
      auto l = py::cast<py::list>(state);
      if (py::cast<bool>(o)) {
        l.insert(0, py::dict());
        return body(*k3, state, effs);
      } else {
        return k(o);
      }
    });
    *k3 = py::cpp_function([state, effs, k2, cond](const object &o) {
      auto l = py::cast<py::list>(state);
      l.attr("pop")(0);
      return cond(k2, state, effs);
    });
    return cond(k2, state, effs);
  }

  inline object ____case(const cont &k, states state, effects effs, const object &ce,
                         const std::vector<object> &conds,
                         const std::vector<object> &exprs) {
    for (unsigned i=0; i<conds.size(); ++i) {
      const auto &p = conds[i];
      const auto &e = exprs[i];
      auto l = py::cast<py::list>(state);
      l.insert(0, py::dict());
      const cont k2 = py::cpp_function([state, k](const object &o) {
        auto l = py::cast<py::list>(state);
        l.attr("pop")(0);
        return k(o);
      });
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
    return handler(py::cpp_function([state](const object &x) { auto l = py::cast<py::list>(state); l.attr("pop")(0); return x;}), state, effs);
  }

  inline object cone__resume(const cont &k, states s, effects effs, const object &a) {
    auto l = py::cast<py::list>(s);
    auto m = py::cast<py::dict>(l[0]);
    return k(m[____resumed_k](a));
  }

}