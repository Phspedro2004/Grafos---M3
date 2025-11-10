// Alunos: Pedro Schneider, Isadora e Kirsten Luz
// Compilação: g++ -o main main.cpp

#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <limits>
#include <queue>
#include <algorithm>
#include <fstream>
#include <iomanip>
using namespace std;

inline int** criarMatriz(int qntV) {
    int** mat = new int*[qntV];
    for (int i = 0; i < qntV; i++) {
        mat[i] = new int[qntV](); 
    }
    return mat;
}
inline void liberarMatriz(int** mat, int qntV) {
    for (int i = 0; i < qntV; i++) delete[] mat[i];
    delete[] mat;
}

// ---------------- buscar índice por rótulo ----------------
int buscarIndice(const vector<string>& rotulos, const string& valor) {
    for (int i = 0; i < (int)rotulos.size(); i++)
        if (rotulos[i] == valor) return i;
    return -1;
}

// ---------------- leitura de predecessores ----------------
vector<int> lerPredecessores(const string& linha, const vector<string>& rotulos) {
    vector<int> preds;
    string s = linha;
    if (s == "-") return preds;
    stringstream ss(s);
    string item;
    while (getline(ss, item, ',')) {
        int idx = buscarIndice(rotulos, item);
        if (idx != -1) preds.push_back(idx);
        else preds.push_back(-1); 
    }
    return preds;
}

// ---------------- ordenação topológica (Kahn) ----------------
// Se houver ciclo, retorna false.
bool topoOrdenacao(int** mat, int qntV, vector<int>& ordem) {
    vector<int> indeg(qntV, 0);
    for (int i = 0; i < qntV; i++)
        for (int j = 0; j < qntV; j++)
            if (mat[i][j]) indeg[j]++;
    queue<int> q;
    for (int i = 0; i < qntV; i++) if (indeg[i] == 0) q.push(i);
    while (!q.empty()) {
        int u = q.front(); q.pop();
        ordem.push_back(u);
        for (int v = 0; v < qntV; v++) if (mat[u][v]) {
            indeg[v]--;
            if (indeg[v] == 0) q.push(v);
        }
    }
    return ((int)ordem.size() == qntV);
}

// ---------------- cálculo PERT/CPM ----------------
bool calcularPERT(int** mat, int qntV, const vector<string>& rotulos, const vector<int>& dur,
                  vector<int>& ES, vector<int>& EF, vector<int>& LS, vector<int>& LF, int& duracaoProjeto) {

    vector<int> ordem;
    if (!topoOrdenacao(mat, qntV, ordem)) return false;

    // -------- forward (ES/EF) --------
    ES.assign(qntV, 0);
    EF.assign(qntV, 0);
    for (int idx = 0; idx < qntV; idx++) {
        int u = ordem[idx];
        int maxEfPred = 0;
       
        for (int p = 0; p < qntV; p++)
            if (mat[p][u]) maxEfPred = max(maxEfPred, EF[p]);
        ES[u] = maxEfPred;
        EF[u] = ES[u] + dur[u];
    }

    duracaoProjeto = 0;
    for (int i = 0; i < qntV; i++) duracaoProjeto = max(duracaoProjeto, EF[i]);

    // -------- backward (LS/LF) --------
    LF.assign(qntV, numeric_limits<int>::max());
    LS.assign(qntV, 0);
    for (int i = 0; i < qntV; i++) {
        bool temSuc = false;
        for (int j = 0; j < qntV; j++) if (mat[i][j]) { temSuc = true; break; }
        if (!temSuc) LF[i] = duracaoProjeto;
    }

    for (int idx = qntV - 1; idx >= 0; idx--) {
        int u = ordem[idx];
        int minLsSuc = numeric_limits<int>::max();
        bool temSuc = false;
        for (int v = 0; v < qntV; v++) if (mat[u][v]) {
            temSuc = true;
            minLsSuc = min(minLsSuc, LF[v] - dur[v]);
        }
        if (temSuc) LF[u] = minLsSuc;
        LS[u] = LF[u] - dur[u];
    }
    return true;
}

// ---------------- encontrar um caminho crítico ----------------
vector<int> encontrarCaminhoCritico(int** mat, int qntV, const vector<int>& ES, const vector<int>& EF, const vector<int>& LS, const vector<int>& LF) {
    vector<int> floatTotal(qntV);
    for (int i = 0; i < qntV; i++) floatTotal[i] = LS[i] - ES[i];

    vector<int> starts;
    for (int i = 0; i < qntV; i++) {
        bool temPred = false;
        for (int p = 0; p < qntV; p++){
            if (mat[p][i]) { 
                temPred = true; 
                break;
            }
        }
        if (!temPred && floatTotal[i] == 0) {
            starts.push_back(i);
        }
    }

    int inicio = -1;
    if (!starts.empty()) inicio = starts[0];
    else {
        for (int i = 0; i < qntV; i++){
            if (floatTotal[i] == 0) { 
                inicio = i; break; 
            }
        }   
    }

    vector<int> caminho;
    if (inicio == -1) {
        return caminho; 
    }
    int cur = inicio;
    caminho.push_back(cur);
    while (true) {
        int proximo = -1;
        for (int v = 0; v < qntV; v++) {
            if (mat[cur][v] && (LS[v] - ES[v] == 0) && ES[v] == EF[cur]) {
                proximo = v;
                break;
            }
        }
        if (proximo == -1) break;
        caminho.push_back(proximo);
        cur = proximo;
    }
    return caminho;
}

// ---------------- gerar JSON para visualização externa ----------------
void gerarJSON_vis(int** mat, int qntV,
                   const vector<string>& rotulos,
                   const vector<int>& dur,
                   const vector<int>& caminhoCrit,
                   const vector<int>& ES, const vector<int>& EF,
                   const vector<int>& LS, const vector<int>& LF) {

    vector<pair<string, string>> critEdges;
    auto folga = [&](int i){ return LS[i] - ES[i]; };
    for (int u = 0; u < qntV; u++) {
        for (int v = 0; v < qntV; v++) {
            if (mat[u][v] && folga(u)==0 && folga(v)==0 && ES[v]==EF[u]) {
                critEdges.emplace_back(rotulos[u], rotulos[v]);
            }
        }
    }

    ofstream f("grafo.json");
    if (!f.is_open()) {
        cerr << "Aviso: não foi possível criar grafo.json.\n";
        return;
    }

    f << "{\n";
    f << "  \"nodes\": [\n";
    for (int i = 0; i < qntV; i++) {
        f << "    {\"id\": " << quoted(rotulos[i]) << ", \"duration\": " << dur[i] << "}";
        if (i != qntV - 1) f << ",";
        f << "\n";
    }
    f << "  ],\n";

    f << "  \"edges\": [\n";
    bool first = true;
    auto writeComma = [&](bool &first) { if (!first) f << ",\n"; else first = false; };

    for (int i = 0; i < qntV; i++) {
        for (int j = 0; j < qntV; j++) {
            if (mat[i][j]) {
                writeComma(first);
                f << "    {\"from\": " << quoted(rotulos[i]) << ", \"to\": " << quoted(rotulos[j]) << "}";
            }
        }
    }
    f << "\n  ],\n";

    f << "  \"critical_path\": [\n";
    for (int i = 0; i < (int)caminhoCrit.size(); i++) {
        f << "    " << quoted(rotulos[caminhoCrit[i]]);
        if (i != (int)caminhoCrit.size() - 1) f << ",";
        f << "\n";
    }
    f << "  ],\n";

    f << "  \"critical_edges\": [\n";
    for (size_t i = 0; i < critEdges.size(); ++i) {
        f << "    {\"from\": " << quoted(critEdges[i].first) << ", \"to\": " << quoted(critEdges[i].second) << "}";
        if (i != critEdges.size() - 1) f << ",";
        f << "\n";
    }
    f << "  ]\n";

    f << "}\n";
    f.close();
}

// ---------------- main ----------------
int main() {
    cout << "=== PERT/CPM (vértices = atividades) ===\n\n";
    int n;
    cout << "Quantidade de atividades: ";
    while (!(cin >> n) || n <= 0) {
        cout << "Entrada inválida. Digite um inteiro > 0: ";
        cin.clear();
        cin.ignore(numeric_limits<streamsize>::max(), '\n');
    }
    cin.ignore(numeric_limits<streamsize>::max(), '\n');

    vector<string> rotulos(n);
    vector<int> dur(n, 0);
    vector<vector<int>> preds_raw(n);

    cout << "\nDigite os rótulos:\n";
    for (int i = 0; i < n; i++) {
        cout << "Rótulo atividade " << i+1 << ": ";
        cin >> rotulos[i];
    }

    cout << "\nDigite as durações:\n";
    for (int i = 0; i < n; i++) {
        cout << "Duração de " << rotulos[i] << ": ";
        while (!(cin >> dur[i]) || dur[i] < 0) {
            cout << "Duração inválida. Digite inteiro >= 0: ";
            cin.clear();
            cin.ignore(numeric_limits<streamsize>::max(), '\n');
        }
    }

    cin.ignore(numeric_limits<streamsize>::max(), '\n');

    cout << "\nDigite os predecessores para cada atividade.\nExemplo: A,B ou '-' se nenhum.\n";
    for (int i = 0; i < n; i++) {
        cout << "Predecessores de " << rotulos[i] << " : ";
        string linha;
        getline(cin, linha);
        if (linha.empty()) { i--; continue; }
        vector<int> pl = lerPredecessores(linha, rotulos);
        bool valido = true;
        for (int x : pl) if (x == -1) { valido = false; break; }
        if (!valido) {
            cout << "Um ou mais rótulos não existem. Digite novamente.\n";
            i--;
            continue;
        }
        preds_raw[i] = pl;
    }

    int** mat = criarMatriz(n);
    for (int i = 0; i < n; i++)
        for (int p : preds_raw[i])
            mat[p][i] = 1;

    cout << "\nGrafo construído. Matriz de adjacência:\n";
    cout << "   ";
    for (int j = 0; j < n; j++) cout << j << " ";
    cout << "\n";
    for (int i = 0; i < n; i++) {
        cout << i << ": ";
        for (int j = 0; j < n; j++) cout << mat[i][j] << " ";
        cout << "   (" << rotulos[i] << ", d=" << dur[i] << ")\n";
    }

    vector<int> ES, EF, LS, LF;
    int durProjeto = 0;
    bool ok = calcularPERT(mat, n, rotulos, dur, ES, EF, LS, LF, durProjeto);
    if (!ok) {
        cout << "\nErro: o grafo possui ciclo(s).\n";
        liberarMatriz(mat, n);
        return 0;
    }

    vector<int> folga(n);
    for (int i = 0; i < n; i++) folga[i] = LS[i] - ES[i];

    cout << "\nTabela PERT/CPM:\n";
    cout << "Atv | Dur | ES | EF | LS | LF | Folga\n";
    cout << "-------------------------------------------\n";
    for (int i = 0; i < n; i++) {
        printf("%-3s | %-3d | %-3d | %-3d | %-3d | %-3d | %-3d\n",
               rotulos[i].c_str(), dur[i], ES[i], EF[i], LS[i], LF[i], folga[i]);
    }
    cout << "-------------------------------------------\n";
    cout << "Duração mínima: " << durProjeto << "\n";

    cout << "\nAtividades críticas (folga total = 0):\n";
    vector<int> criticas;
    for (int i = 0; i < n; i++) if (folga[i] == 0) {
        criticas.push_back(i);
        cout << rotulos[i] << " ";
    }
    if (criticas.empty()) cout << "(nenhuma)\n";
    cout << "\n";

    vector<int> caminhoCrit = encontrarCaminhoCritico(mat, n, ES, EF, LS, LF);
    if (!caminhoCrit.empty()) {
        cout << "Caminho crítico: ";
        for (int i = 0; i < (int)caminhoCrit.size(); i++) {
            if (i) cout << " -> ";
            cout << rotulos[caminhoCrit[i]];
        }
        cout << "\n";
    } else {
        cout << "Não foi possível extrair um caminho crítico linear.\n";
    }

    gerarJSON_vis(mat, n, rotulos, dur, caminhoCrit, ES, EF, LS, LF);
    cout << "Arquivo 'grafo.json' gerado.\n";

    liberarMatriz(mat, n);
    return 0;
}
