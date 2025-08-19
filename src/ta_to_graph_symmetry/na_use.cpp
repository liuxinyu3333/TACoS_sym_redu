// test_digraph.cpp
#include <iostream>
#include "digraph.hh"  // 来自 /home/xinyuliu/bliss-0.77/src

// 回调函数，每当发现一个自动同构映射时调用
// 参数 n 为图中顶点的数量，perm 为长度为 n 的自动同构映射数组
void automorphism_callback(unsigned int n, const unsigned int* perm) {
    std::cout << "Found automorphism mapping:" << std::endl;
    for (unsigned int i = 0; i < n; i++) {
        std::cout << i << " -> " << perm[i] << std::endl;
    }
    std::cout << std::endl;
}

int main() {
    // 创建一个有向图对象
    bliss::Digraph g;
    
    // 添加顶点，并在添加时指定颜色
    // 例如，将 v0 和 v1 分为一组（颜色 0），将 v2 和 v3 分为另一组（颜色 1）
    auto v0 = g.add_vertex(0);
    auto v1 = g.add_vertex(0);
    auto v2 = g.add_vertex(1);
    auto v3 = g.add_vertex(1);

    // 添加有向边：0->1, 1->2, 2->0, 2->3
    g.add_edge(v0, v1);
    g.add_edge(v1, v2);
    g.add_edge(v2, v0);
    g.add_edge(v2, v3);

    // 定义一个空的 Stats 对象
    bliss::Stats stats;

    // 调用自动同构检测
    // find_automorphisms 接受三个参数：Stats 对象、回调函数、以及一个控制是否继续搜索的函数（这里始终返回 true）
    g.find_automorphisms(stats, automorphism_callback, []() { return true; });

    std::cout << "Bliss directed graph automorphism test completed." << std::endl;
    return 0;
}
