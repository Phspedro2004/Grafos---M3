// pert_cpm.cpp
// Programa PERT/CPM (vértices = atividades)
// Entrada: rótulo, duração, predecessores
// Saída: ES, EF, LS, LF, Folga, Caminho crítico
// Compilar: g++ -std=c++17 pert_cpm.cpp -o pert_cpm

#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <limits>
#include <queue>
#include <algorithm>
#include <fstream>
using namespace std;

// ---------------- utilidades de matriz (estilo do seu projeto) ----------------
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

// ---------------- buscar índice ----------------
int buscarIndice(const vector<string>& rotulos, const string& valor) {
    for (int i = 0; i < (int)rotulos.size(); i++)
        if (rotulos[i] == valor) return i;
    return -1;
}

// ---------------- leitura de predecessores (linha como "A,B,C" ou "-" para nenhum) ----------------
vector<int> lerPredecessores(const string& linha, const vector<string>& rotulos) {
    vector<int> preds;
    string s = linha;
    // remove espaços
    s.erase(remove_if(s.begin(), s.end(), ::isspace), s.end());
    if (s.empty() || s == "-" ) return preds;
    stringstream ss(s);
    string item;
    while (getline(ss, item, ',')) {
        int idx = buscarIndice(rotulos, item);
        if (idx != -1) preds.push_back(idx);
        else {
            // se rótulo não existir, retornamos -1 como sinalizador (tratado pelo chamador)
            preds.push_back(-1);
        }
    }
    return preds;
}

// ---------------- topological sort (Kahn) ----------------
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
    return ((int)ordem.size() == qntV); // true se DAG, false se ciclo
}

// ---------------- calcular ES/EF (forward) e LS/LF (backward) ----------------
bool calcularPERT(int** mat, int qntV, const vector<string>& rotulos, const vector<int>& dur,
                  vector<int>& ES, vector<int>& EF, vector<int>& LS, vector<int>& LF, int& duracaoProjeto) {

    vector<int> ordem;
    if (!topoOrdenacao(mat, qntV, ordem)) return false; // ciclo detectado

    // forward pass
    ES.assign(qntV, 0);
    EF.assign(qntV, 0);
    for (int idx = 0; idx < qntV; idx++) {
        int u = ordem[idx];
        int maxEfPred = 0;
        // buscar predecessores (mat[i][u] == 1)
        for (int p = 0; p < qntV; p++)
            if (mat[p][u]) maxEfPred = max(maxEfPred, EF[p]);
        ES[u] = maxEfPred;
        EF[u] = ES[u] + dur[u];
    }
    duracaoProjeto = 0;
    for (int i = 0; i < qntV; i++) duracaoProjeto = max(duracaoProjeto, EF[i]);

    // backward pass
    LF.assign(qntV, numeric_limits<int>::max());
    LS.assign(qntV, 0);
    // inicializar LF dos nós finais (aqueles sem sucessores) com duração do projeto
    for (int i = 0; i < qntV; i++) {
        bool temSuc = false;
        for (int j = 0; j < qntV; j++) if (mat[i][j]) { temSuc = true; break; }
        if (!temSuc) LF[i] = duracaoProjeto;
    }
    // processar na ordem inversa topológica
    for (int idx = qntV-1; idx >= 0; idx--) {
        int u = ordem[idx];
        // se LF ainda é infinito (nó com sucessores), calcular min LS de sucessores
        int minLsSuc = numeric_limits<int>::max();
        bool temSuc = false;
        for (int v = 0; v < qntV; v++) if (mat[u][v]) {
            temSuc = true;
            minLsSuc = min(minLsSuc, LF[v] - 0); // LF[v] já é tempo limite de fim de v
        }
        if (temSuc) LF[u] = minLsSuc;
        LS[u] = LF[u] - dur[u];
    }
    return true;
}

// ---------------- encontrar um caminho crítico (sequência ES/EF com folga 0) ----------------
vector<int> encontrarCaminhoCritico(int** mat, int qntV, const vector<int>& ES, const vector<int>& EF, const vector<int>& LS, const vector<int>& LF) {
    vector<int> floatTotal(qntV);
    for (int i = 0; i < qntV; i++) floatTotal[i] = LS[i] - ES[i];

    // iniciar por quaisquer vértices sem predecessores (start) que tenham float 0
    vector<int> starts;
    for (int i = 0; i < qntV; i++) {
        bool temPred = false;
        for (int p = 0; p < qntV; p++) if (mat[p][i]) { temPred = true; break; }
        if (!temPred && floatTotal[i] == 0) starts.push_back(i);
    }
    // se não houver starts com float 0, procurar qualquer vértice com float 0 como início
    int inicio = -1;
    if (!starts.empty()) inicio = starts[0];
    else {
        for (int i = 0; i < qntV; i++) if (floatTotal[i] == 0) { inicio = i; break; }
    }
    vector<int> caminho;
    if (inicio == -1) return caminho;

    int cur = inicio;
    caminho.push_back(cur);
    // caminhar por sucessores que também tenham float 0 e onde ES do sucessor == EF do atual (sequência direta)
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

// ---------------- gerar JSON (visualização simples) ----------------
void gerarJSON(int** mat, int qntV, const vector<string>& rotulos) {
    FILE* f = fopen("grafo.json", "w");
    if (!f) return;
    fprintf(f, "{\n  \"vertices\": [\n");
    for (int i = 0; i < qntV; i++) {
        fprintf(f, "    {\"id\": %d, \"label\": \"%s\"}%s\n", i, rotulos[i].c_str(), (i==qntV-1? "":" ,"));
    }
    fprintf(f, "  ],\n  \"arestas\": [\n");
    bool first = true;
    for (int i = 0; i < qntV; i++)
        for (int j = 0; j < qntV; j++)
            if (mat[i][j]) {
                if (!first) fprintf(f, ",\n");
                fprintf(f, "    {\"from\": %d, \"to\": %d}", i, j);
                first = false;
            }
    fprintf(f, "\n  ]\n}\n");
    fclose(f);
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

    cout << "\nDigite os rótulos (identificadores curtos, ex: A B C1):\n";
    for (int i = 0; i < n; i++) {
        cout << "Rótulo atividade " << i+1 << ": ";
        cin >> rotulos[i];
    }
    cout << "\nDigite as durações (inteiro >=0) na ordem das atividades:\n";
    for (int i = 0; i < n; i++) {
        cout << "Duração de " << rotulos[i] << ": ";
        while (!(cin >> dur[i]) || dur[i] < 0) {
            cout << "Duração inválida. Digite inteiro >= 0: ";
            cin.clear();
            cin.ignore(numeric_limits<streamsize>::max(), '\n');
        }
    }
    cin.ignore(numeric_limits<streamsize>::max(), '\n');
    cout << "\nAgora digite os predecessores para cada atividade.\n"
         << "Formato: lista separada por vírgula sem espaços (ex: A,B) ou '-' se nenhum.\n";
    for (int i = 0; i < n; i++) {
        cout << "Predecessores de " << rotulos[i] << " : ";
        string linha;
        getline(cin, linha);
        if (linha.empty()) { i--; continue; } // garantir leitura correta
        // parse e validar
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

    // construir matriz adj (aresta p -> i se p é predecessor de i)
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

    // calcular PERT/CPM
    vector<int> ES, EF, LS, LF;
    int durProjeto = 0;
    bool ok = calcularPERT(mat, n, rotulos, dur, ES, EF, LS, LF, durProjeto);
    if (!ok) {
        cout << "\nErro: o grafo possui ciclo(s). PERT/CPM exige DAG (sem ciclo de precedência).\n";
        liberarMatriz(mat, n);
        return 0;
    }

    vector<int> folga(n);
    for (int i = 0; i < n; i++) folga[i] = LS[i] - ES[i];

    // imprimir tabela (notação min/max inicio/fim)
    cout << "\nTabela PERT/CPM (tempos em unidades de duração):\n";
    cout << "Atv | Dur | ES(min start) | EF(min finish) | LS(max start) | LF(max finish) | Folga\n";
    cout << "--------------------------------------------------------------------------\n";
    for (int i = 0; i < n; i++) {
        printf("%-3s | %-3d | %-13d | %-13d | %-12d | %-13d | %-5d\n",
               rotulos[i].c_str(), dur[i], ES[i], EF[i], LS[i], LF[i], folga[i]);
    }
    cout << "--------------------------------------------------------------------------\n";
    cout << "Duração mínima do projeto: " << durProjeto << "\n";

    // identificar atividades críticas
    cout << "\nAtividades críticas (folga total = 0):\n";
    vector<int> criticas;
    for (int i = 0; i < n; i++) if (folga[i] == 0) {
        criticas.push_back(i);
        cout << rotulos[i] << " ";
    }
    if (criticas.empty()) cout << "(nenhuma)\n";
    cout << "\n";

    // encontrar um caminho crítico
    vector<int> caminhoCrit = encontrarCaminhoCritico(mat, n, ES, EF, LS, LF);
    if (!caminhoCrit.empty()) {
        cout << "Um caminho crítico (sequência de atividades): ";
        for (int i = 0; i < (int)caminhoCrit.size(); i++) {
            if (i) cout << " -> ";
            cout << rotulos[caminhoCrit[i]];
        }
        cout << "\n";
    } else {
        cout << "Não foi possível extrair um caminho crítico linear (pode haver múltiplos caminhos críticos paralelos).\n";
    }

    // gerar JSON para visualização externa
    gerarJSON(mat, n, rotulos);
    cout << "\nArquivo 'grafo.json' gerado para visualização (opcional).\n";

    liberarMatriz(mat, n);
    cout << "\nPronto. Apresente explicando:\n"
         << "- Como inseriu as atividades (rótulo, duração, predecessores).\n"
         << "- O cálculo: forward pass (ES/EF) e backward pass (LS/LF).\n"
         << "- Como identificar folgas e atividades críticas (folga = 0).\n";
    return 0;
}
